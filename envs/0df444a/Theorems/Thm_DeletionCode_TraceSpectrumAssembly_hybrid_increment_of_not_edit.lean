-- Prove2me | Theorems.Thm_DeletionCode_TraceSpectrumAssembly_hybrid_increment_of_not_edit
-- name    : DeletionCode.TraceSpectrumAssembly.hybrid_increment_of_not_edit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:48:33.265006+00:00
-- url     : https://prove2.me/theorems/90e775d0-c7c6-4246-ade4-4b8ac28134a4
-- title:
--   Trace Spectrum Assembly: hybrid increment of not edit
-- statement:
--   Matched columns contribute zero, derived from their actual projections.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSpectrumAssembly.lean#L48-L58
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSpectrumAssembly.lean#L48-L58

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Definitions.Def_DeletionCode_SpectrumPrefixChange
import Definitions.Def_DeletionCode_TraceSpectrumAssembly
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSpectrumAssembly
open AlignmentTrace FiniteConflictGraph TraceEditData SignedSupport
open SpectrumPrefixChange TraceMatchedSuffix
open scoped BigOperators

theorem DeletionCode.TraceSpectrumAssembly.hybrid_increment_of_not_edit (trace : Trace) (i : Fin trace.length)
    (hnot : ¬ EditIndex trace i) (L : ℕ) (g : Gram L) :
    spectrum (hybrid trace (i.val + 1)) L g - spectrum (hybrid trace i.val) L g = 0 := by sorry
