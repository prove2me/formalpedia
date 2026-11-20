-- Prove2me | Theorems.Thm_DeletionCode_TraceSpectrumAssembly_hybrid_before
-- name    : DeletionCode.TraceSpectrumAssembly.hybrid_before
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:48:55.860108+00:00
-- url     : https://prove2.me/theorems/46d15dcc-21d3-46a9-8e84-d51ae22f623c
-- title:
--   Trace Spectrum Assembly: hybrid before
-- statement:
--   The Trace Spectrum Assembly construction uses the hybrid before property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSpectrumAssembly.lean#L29-L37
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSpectrumAssembly.lean#L29-L37

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Definitions.Def_DeletionCode_SpectrumPrefixChange
import Definitions.Def_DeletionCode_TraceSpectrumAssembly
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSpectrumAssembly
open AlignmentTrace FiniteConflictGraph TraceEditData SignedSupport
open SpectrumPrefixChange TraceMatchedSuffix
open scoped BigOperators

theorem DeletionCode.TraceSpectrumAssembly.hybrid_before (trace : Trace) (i : Fin trace.length) :
    hybrid trace i.val = Trace.target (trace.take i.val) ++
      (Trace.source [trace.get i] ++ Trace.source (trace.drop (i.val + 1))) := by sorry
