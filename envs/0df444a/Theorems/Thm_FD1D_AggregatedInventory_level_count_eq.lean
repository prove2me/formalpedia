-- Prove2me | Theorems.Thm_FD1D_AggregatedInventory_level_count_eq
-- name    : FD1D.AggregatedInventory.level_count_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:49:42.280263+00:00
-- url     : https://prove2.me/theorems/8b7d69ed-4fc1-4aca-beb6-6387018b22cf
-- title:
--   Aggregated Inventory: level count eq
-- statement:
--   The Aggregated Inventory construction uses the level count eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L351-L359
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L351-L359

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.AggregatedInventory.level_count_eq
    {L m : ℕ} (I : AggregatedInventory L m) {d : ℕ} (hdL : d ≤ L) :
    ∑ v, I.count d v = m := by sorry
