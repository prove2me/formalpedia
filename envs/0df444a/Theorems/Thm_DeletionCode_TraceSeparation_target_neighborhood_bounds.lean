-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_target_neighborhood_bounds
-- name    : DeletionCode.TraceSeparation.target_neighborhood_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:36:47.541417+00:00
-- url     : https://prove2.me/theorems/a8504cf3-a58b-4109-ada7-aa11dd997f44
-- title:
--   Trace Separation: target neighborhood bounds
-- statement:
--   The Trace Separation construction uses the target neighborhood bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L153-L158
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L153-L158

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.target_neighborhood_bounds {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    neighborhoodLeft L (trace.targetPosition i.val) + 2 * L =
        neighborhoodRight L (trace.targetPosition i.val) ∧
      neighborhoodRight L (trace.targetPosition i.val) ≤ trace.target.length := by sorry
