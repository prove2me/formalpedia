-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_targetPosition_separated
-- name    : DeletionCode.TraceSeparation.targetPosition_separated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:37:25.60734+00:00
-- url     : https://prove2.me/theorems/39646966-edb8-4371-ac80-ae3a99393819
-- title:
--   Trace Separation: target Position separated
-- statement:
--   The target positions of any ordered pair of edits retain the full gap B.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L102-L106
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L102-L106

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.targetPosition_separated {trace : Trace} {B : ℕ}
    (hsep : Separated B trace) (i j : Fin trace.length)
    (hi : EditIndex trace i) (hj : EditIndex trace j) (hij : i.val < j.val) :
    trace.targetPosition i.val + B ≤ trace.targetPosition j.val := by sorry
