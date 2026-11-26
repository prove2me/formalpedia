-- Prove2me | Theorems.Thm_FD1D_InventoryState_move_apply_of_pos
-- name    : FD1D.InventoryState.move_apply_of_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:40:08.396239+00:00
-- url     : https://prove2.me/theorems/19751852-d51a-5b79-9ab9-f1a177748519
-- title:
--   Inventory State: move apply of pos
-- statement:
--   The Inventory State construction uses the move apply of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L684-L701
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L684-L701

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.InventoryState
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem FD1D.InventoryState.move_apply_of_pos {m : ℕ} (x : InventoryState ι m) {d a i : ι}
    (hd : 0 < x.1 d) :
    (move x d a).1 i =
      x.1 i + (if i = a then 1 else 0) - (if i = d then 1 else 0) := by sorry
