-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_target_neighborhood_ordered
-- name    : DeletionCode.TraceSeparation.target_neighborhood_ordered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:37:31.184191+00:00
-- url     : https://prove2.me/theorems/fe047bb4-76b3-4d80-a8fc-ddcc90d11dcc
-- title:
--   Trace Separation: target neighborhood ordered
-- statement:
--   The Trace Separation construction uses the target neighborhood ordered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L177-L182
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L177-L182

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.target_neighborhood_ordered {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i j : Fin trace.length)
    (hi : EditIndex trace i) (hj : EditIndex trace j) (hij : i.val < j.val) :
    neighborhoodRight L (trace.targetPosition i.val) ≤
      neighborhoodLeft L (trace.targetPosition j.val) := by sorry
