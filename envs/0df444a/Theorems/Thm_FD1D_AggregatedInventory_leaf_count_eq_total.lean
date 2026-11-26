-- Prove2me | Theorems.Thm_FD1D_AggregatedInventory_leaf_count_eq_total
-- name    : FD1D.AggregatedInventory.leaf_count_eq_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:49:58.680399+00:00
-- url     : https://prove2.me/theorems/2abdd3ae-9e95-552b-9595-8bec7e3114ba
-- title:
--   Aggregated Inventory: leaf count eq total
-- statement:
--   The Aggregated Inventory construction uses the leaf count eq total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L361-L364
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L361-L364

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.AggregatedInventory.leaf_count_eq_total
    {L m : ℕ} (I : AggregatedInventory L m) :
    ∑ v, I.count L v = m := by sorry
