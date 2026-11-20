-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_target_neighborhood_subset
-- name    : DeletionCode.TraceSeparation.target_neighborhood_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:37:39.162942+00:00
-- url     : https://prove2.me/theorems/e045d192-52dd-4732-aefe-cde5d6dd4e26
-- title:
--   Trace Separation: target neighborhood subset
-- statement:
--   The Trace Separation construction uses the target neighborhood subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L165-L168
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L165-L168

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.target_neighborhood_subset {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    neighborhood L (trace.targetPosition i.val) ⊆ Set.Ico 0 trace.target.length := by sorry
