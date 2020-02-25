/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "frontend/Frontend2.h"

#include "mozilla/Maybe.h"                  // mozilla::Maybe
#include "mozilla/OperatorNewExtensions.h"  // mozilla::KnownNotNull
#include "mozilla/Span.h"                   // mozilla::{Span, MakeSpan}

#include <stddef.h>  // size_t
#include <stdint.h>  // uint8_t, uint32_t

#include "jsapi.h"

#include "frontend/AbstractScope.h"    // ScopeIndex
#include "frontend/CompilationInfo.h"  // CompilationInfo
#include "frontend/smoosh_generated.h"  // CVec, SmooshResult, SmooshCompileOptions, free_smoosh, run_smoosh
#include "frontend/SourceNotes.h"  // jssrcnote
#include "frontend/Stencil.h"      // ScopeCreationData
#include "gc/Rooting.h"            // RootedScriptSourceObject
#include "js/HeapAPI.h"            // JS::GCCellPtr
#include "js/RootingAPI.h"         // JS::Handle, JS::Rooted
#include "js/TypeDecls.h"          // Rooted{Script,Value,String,Object}
#include "vm/JSAtom.h"             // AtomizeUTF8Chars
#include "vm/JSScript.h"           // JSScript, ScopeNote
#include "vm/Scope.h"              // BindingName
#include "vm/ScopeKind.h"          // ScopeKind

#include "vm/JSContext-inl.h"  // AutoKeepAtoms (used by BytecodeCompiler)

using mozilla::Utf8Unit;

using namespace js::gc;
using namespace js::frontend;
using namespace js;

namespace js {

namespace frontend {

class SmooshScriptStencil : public ScriptStencil {
  const SmooshResult& result_;
  CompilationInfo& compilationInfo_;
  JSAtom** allAtoms_ = nullptr;

  void init() {
    lineno = result_.lineno;
    column = result_.column;

    natoms = result_.atoms.len;

    ngcthings = result_.gcthings.len;

    numResumeOffsets = 0;
    numScopeNotes = result_.scope_notes.len;
    numTryNotes = 0;

    mainOffset = result_.main_offset;
    nfixed = result_.max_fixed_slots;
    nslots = nfixed + result_.maximum_stack_depth;
    bodyScopeIndex = result_.body_scope_index;
    numICEntries = result_.num_ic_entries;
    numBytecodeTypeSets = result_.num_type_sets;

    strict = result_.strict;
    bindingsAccessedDynamically = result_.bindings_accessed_dynamically;
    hasCallSiteObj = result_.has_call_site_obj;
    isForEval = result_.is_for_eval;
    isModule = result_.is_module;
    isFunction = result_.is_function;
    hasNonSyntacticScope = result_.has_non_syntactic_scope;
    needsFunctionEnvironmentObjects =
        result_.needs_function_environment_objects;
    hasModuleGoal = result_.has_module_goal;

    code = mozilla::MakeSpan(result_.bytecode.data, result_.bytecode.len);
    MOZ_ASSERT(notes.IsEmpty());
  }

 public:
  explicit SmooshScriptStencil(const SmooshResult& result,
                               CompilationInfo& compilationInfo)
      : result_(result), compilationInfo_(compilationInfo) {
    init();
  }

  virtual bool finishGCThings(JSContext* cx,
                              mozilla::Span<JS::GCCellPtr> gcthings) const {
    for (size_t i = 0; i < ngcthings; i++) {
      SmooshGCThing& item = result_.gcthings.data[i];

      switch (item.kind) {
        case SmooshGCThingKind::ScopeIndex: {
          MutableHandle<ScopeCreationData> data =
              compilationInfo_.scopeCreationData[item.scope_index];
          Scope* scope = data.get().createScope(cx);
          if (!scope) {
            return false;
          }

          gcthings[i] = JS::GCCellPtr(scope);

          break;
        }
      }
    }

    return true;
  }

  virtual void initAtomMap(GCPtrAtom* atoms) const {
    for (uint32_t i = 0; i < natoms; i++) {
      size_t index = result_.atoms.data[i];
      atoms[i] = allAtoms_[index];
    }
  }

  virtual void finishResumeOffsets(
      mozilla::Span<uint32_t> resumeOffsets) const {}

  virtual void finishScopeNotes(mozilla::Span<ScopeNote> scopeNotes) const {
    for (size_t i = 0; i < result_.scope_notes.len; i++) {
      SmooshScopeNote& scopeNote = result_.scope_notes.data[i];
      scopeNotes[i].index = scopeNote.index;
      scopeNotes[i].start = scopeNote.start;
      scopeNotes[i].length = scopeNote.length;
      scopeNotes[i].parent = scopeNote.parent;
    }
  }

  virtual void finishTryNotes(mozilla::Span<JSTryNote> tryNotes) const {}

  virtual void finishInnerFunctions() const {}

  bool createAtoms(JSContext* cx) {
    size_t numAtoms = result_.all_atoms.len;

    auto& alloc = compilationInfo_.allocScope.alloc();

    allAtoms_ = alloc.newArray<JSAtom*>(numAtoms);
    if (!allAtoms_) {
      ReportOutOfMemory(cx);
      return false;
    }

    for (size_t i = 0; i < numAtoms; i++) {
      const CVec<uint8_t>& string = result_.all_atoms.data[i];
      JSAtom* atom = AtomizeUTF8Chars(cx, (const char*)string.data, string.len);
      if (!atom) {
        return false;
      }
      allAtoms_[i] = atom;
    }

    return true;
  }

  bool createScopeCreationgData(JSContext* cx) {
    auto& alloc = compilationInfo_.allocScope.alloc();

    for (size_t i = 0; i < result_.scopes.len; i++) {
      SmooshScopeData& scopeData = result_.scopes.data[i];
      size_t numBindings = scopeData.bindings.len;
      ScopeIndex index;

      switch (scopeData.kind) {
        case SmooshScopeDataKind::Global: {
          JS::Rooted<GlobalScope::Data*> data(
              cx, NewEmptyBindingData<GlobalScope>(cx, alloc, numBindings));
          if (!data) {
            return false;
          }

          BindingName* names = data->trailingNames.start();
          for (size_t i = 0; i < numBindings; i++) {
            SmooshBindingName& name = scopeData.bindings.data[i];
            new (mozilla::KnownNotNull, &names[i])
                BindingName(allAtoms_[name.name], name.is_closed_over,
                            name.is_top_level_function);
          }

          data->letStart = scopeData.let_start;
          data->constStart = scopeData.const_start;
          data->length = numBindings;

          if (!ScopeCreationData::create(cx, compilationInfo_,
                                         ScopeKind::Global, data, &index)) {
            return false;
          }
          break;
        }
        case SmooshScopeDataKind::Lexical: {
          JS::Rooted<LexicalScope::Data*> data(
              cx, NewEmptyBindingData<LexicalScope>(cx, alloc, numBindings));
          if (!data) {
            return false;
          }

          BindingName* names = data->trailingNames.start();
          for (size_t i = 0; i < numBindings; i++) {
            SmooshBindingName& name = scopeData.bindings.data[i];
            new (mozilla::KnownNotNull, &names[i])
                BindingName(allAtoms_[name.name], name.is_closed_over,
                            name.is_top_level_function);
          }

          // NOTE: data->nextFrameSlot is set in ScopeCreationData::create.

          data->constStart = scopeData.const_start;
          data->length = numBindings;

          uint32_t firstFrameSlot = scopeData.first_frame_slot;
          ScopeIndex enclosingIndex(scopeData.enclosing);
          Rooted<AbstractScope> enclosing(
              cx, AbstractScope(compilationInfo_, enclosingIndex));
          if (!ScopeCreationData::create(cx, compilationInfo_,
                                         ScopeKind::Lexical, data,
                                         firstFrameSlot, enclosing, &index)) {
            return false;
          }
          break;
        }
      }

      MOZ_ASSERT(index == i);
    }

    return true;
  }
};

// Free given SmooshResult on leaving scope.
class AutoFreeSmooshResult {
  SmooshResult* result_;

 public:
  AutoFreeSmooshResult() = delete;

  AutoFreeSmooshResult(SmooshResult* result) : result_(result) {}
  ~AutoFreeSmooshResult() {
    if (result_) {
      free_smoosh(*result_);
    }
  }
};

void ReportVisageCompileError(JSContext* cx, ErrorMetadata&& metadata,
                              int errorNumber, ...) {
  va_list args;
  va_start(args, errorNumber);
  ReportCompileErrorUTF8(cx, std::move(metadata), /* notes = */ nullptr,
                         JSREPORT_ERROR, errorNumber, &args);
  va_end(args);
}

/* static */
JSScript* Smoosh::compileGlobalScript(CompilationInfo& compilationInfo,
                                      JS::SourceText<Utf8Unit>& srcBuf,
                                      bool* unimplemented) {
  // FIXME: check info members and return with *unimplemented = true
  //        if any field doesn't match to run_smoosh.

  auto bytes = reinterpret_cast<const uint8_t*>(srcBuf.get());
  size_t length = srcBuf.length();

  JSContext* cx = compilationInfo.cx;

  const auto& options = compilationInfo.options;
  SmooshCompileOptions compileOptions;
  compileOptions.no_script_rval = options.noScriptRval;

  SmooshResult smoosh = run_smoosh(bytes, length, &compileOptions);
  AutoFreeSmooshResult afsr(&smoosh);

  if (smoosh.error.data) {
    *unimplemented = false;
    ErrorMetadata metadata;
    metadata.filename = "<unknown>";
    metadata.lineNumber = 1;
    metadata.columnNumber = 0;
    metadata.isMuted = false;
    ReportVisageCompileError(cx, std::move(metadata),
                             JSMSG_VISAGE_COMPILE_ERROR,
                             reinterpret_cast<const char*>(smoosh.error.data));
    return nullptr;
  }

  if (smoosh.unimplemented) {
    *unimplemented = true;
    return nullptr;
  }

  *unimplemented = false;

  RootedScriptSourceObject sso(cx,
                               frontend::CreateScriptSourceObject(cx, options));
  if (!sso) {
    return nullptr;
  }

  RootedObject proto(cx);
  if (!GetFunctionPrototype(cx, GeneratorKind::NotGenerator,
                            FunctionAsyncKind::SyncFunction, &proto)) {
    return nullptr;
  }

  SourceExtent extent(/* sourceStart = */ 0,
                      /* sourceEnd = */ length,
                      /* toStringStart = */ 0,
                      /* toStringEnd = */ length,
                      /* lineno = */ 1,
                      /* column = */ 0);
  RootedScript script(cx,
                      JSScript::Create(cx, cx->global(), options, sso, extent));

  SmooshScriptStencil stencil(smoosh, compilationInfo);
  if (!stencil.createAtoms(cx)) {
    return nullptr;
  }

  if (!stencil.createScopeCreationgData(cx)) {
    return nullptr;
  }

  if (!JSScript::fullyInitFromStencil(cx, script, stencil)) {
    return nullptr;
  }

#if defined(DEBUG) || defined(JS_JITSPEW)
  Sprinter sprinter(cx);
  if (!sprinter.init()) {
    return nullptr;
  }
  if (!Disassemble(cx, script, true, &sprinter, DisassembleSkeptically::Yes)) {
    return nullptr;
  }
  printf("%s\n", sprinter.string());
  if (!Disassemble(cx, script, true, &sprinter, DisassembleSkeptically::No)) {
    return nullptr;
  }
  // (don't bother printing it)
#endif

  return script;
}

bool SmooshParseScript(JSContext* cx, const uint8_t* bytes, size_t length) {
  if (test_parse_script(bytes, length)) {
    return true;
  }
  JS_ReportErrorASCII(cx, "Smoosh parse script failed");
  return false;
}

bool SmooshParseModule(JSContext* cx, const uint8_t* bytes, size_t length) {
  if (test_parse_module(bytes, length)) {
    return true;
  }
  JS_ReportErrorASCII(cx, "Smoosh parse module failed");
  return false;
}

}  // namespace frontend

}  // namespace js
