-- Prove2me | Theorems.Thm_FD1D_assignmentCount_perm
-- name    : FD1D.assignmentCount_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:04:53.674105+00:00
-- url     : https://prove2.me/theorems/dcfb5725-b467-588e-84ac-6c7be604b464
-- title:
--   FD1 D: assignment Count perm
-- statement:
--   Relabeling an assignment relabels its fiber-count state.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Initialization.lean#L98-L101
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Initialization.lean#L98-L101

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Initialization
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators

theorem FD1D.assignmentCount_perm {ι : Type*} [DecidableEq ι]
    {m : ℕ} (e : Equiv.Perm ι) (ω : Assignment ι m) (i : ι) :
    assignmentCount (assignmentPerm e ω) (e i) = assignmentCount ω i := by sorry
