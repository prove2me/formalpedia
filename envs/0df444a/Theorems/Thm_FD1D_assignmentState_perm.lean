-- Prove2me | Theorems.Thm_FD1D_assignmentState_perm
-- name    : FD1D.assignmentState_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:31.901279+00:00
-- url     : https://prove2.me/theorems/32402cba-7ad6-41d7-9a6e-42e3ea814400
-- title:
--   FD1 D: assignment State perm
-- statement:
--   The assignment-to-state map is equivariant for the canonical lifts.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Initialization.lean#L104-L113
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Initialization.lean#L104-L113

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Initialization
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators

theorem FD1D.assignmentState_perm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (e : Equiv.Perm ι) (ω : Assignment ι m) :
    assignmentState (assignmentPerm e ω) =
      inventoryStatePerm e (assignmentState ω) := by sorry
