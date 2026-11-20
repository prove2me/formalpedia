-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_target_neighborhood_disjoint
-- name    : DeletionCode.TraceSeparation.target_neighborhood_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:37:26.996626+00:00
-- url     : https://prove2.me/theorems/c5f4e871-843c-46a9-b924-78de461f86be
-- title:
--   Trace Separation: target neighborhood disjoint
-- statement:
--   The corresponding target neighborhoods are disjoint as well.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L197-L206
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L197-L206

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.target_neighborhood_disjoint {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i j : Fin trace.length)
    (hi : EditIndex trace i) (hj : EditIndex trace j) (hne : i ≠ j) :
    Disjoint (neighborhood L (trace.targetPosition i.val))
      (neighborhood L (trace.targetPosition j.val)) := by sorry
