-- Prove2me | Theorems.Thm_FD1D_DeletionRule_kernel_move_pos
-- name    : FD1D.DeletionRule.kernel_move_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:40:56.176493+00:00
-- url     : https://prove2.me/theorems/ca9300aa-7733-4fcd-a8ff-728bbfb8d194
-- title:
--   Deletion Rule: kernel move pos
-- statement:
--   Every legal delete/arrive move has positive one-step probability.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L768-L810
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L768-L810

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.DeletionRule
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {m : ℕ}

theorem FD1D.DeletionRule.kernel_move_pos (R : DeletionRule ι m)
    (x : InventoryState ι m) {d a : ι} (hd : 0 < x.1 d) :
    0 < R.kernel x (InventoryState.move x d a) := by sorry
