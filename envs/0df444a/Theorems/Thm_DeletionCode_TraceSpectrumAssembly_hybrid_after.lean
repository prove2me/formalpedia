-- Prove2me | Theorems.Thm_DeletionCode_TraceSpectrumAssembly_hybrid_after
-- name    : DeletionCode.TraceSpectrumAssembly.hybrid_after
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:49:04.280639+00:00
-- url     : https://prove2.me/theorems/da279178-10f8-4550-9230-01c88f365be6
-- title:
--   Trace Spectrum Assembly: hybrid after
-- statement:
--   The Trace Spectrum Assembly construction uses the hybrid after property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSpectrumAssembly.lean#L39-L45
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSpectrumAssembly.lean#L39-L45

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Definitions.Def_DeletionCode_SpectrumPrefixChange
import Definitions.Def_DeletionCode_TraceSpectrumAssembly
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSpectrumAssembly
open AlignmentTrace FiniteConflictGraph TraceEditData SignedSupport
open SpectrumPrefixChange TraceMatchedSuffix
open scoped BigOperators

theorem DeletionCode.TraceSpectrumAssembly.hybrid_after (trace : Trace) (i : Fin trace.length) :
    hybrid trace (i.val + 1) =
      (Trace.target (trace.take i.val) ++ Trace.target [trace.get i]) ++
        Trace.source (trace.drop (i.val + 1)) := by sorry
