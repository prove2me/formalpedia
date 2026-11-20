-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_source_neighborhood_subset
-- name    : DeletionCode.TraceSeparation.source_neighborhood_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:37:31.675175+00:00
-- url     : https://prove2.me/theorems/c3162cd3-e9c8-445b-b7c3-45da14b23988
-- title:
--   Trace Separation: source neighborhood subset
-- statement:
--   The Trace Separation construction uses the source neighborhood subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L160-L163
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L160-L163

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.source_neighborhood_subset {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    neighborhood L (trace.sourcePosition i.val) ⊆ Set.Ico 0 trace.source.length := by sorry
