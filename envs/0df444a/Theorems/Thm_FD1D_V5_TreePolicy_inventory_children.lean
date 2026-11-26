-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_inventory_children
-- name    : FD1D.V5.TreePolicy.inventory_children
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:51:07.711798+00:00
-- url     : https://prove2.me/theorems/99e97115-ae8b-4c6f-8fb6-fea1d3aa9670
-- title:
--   Tree Policy: inventory children
-- statement:
--   The Tree Policy construction uses the inventory children property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L101-L107
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L101-L107

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.inventory_children (I : AggregatedInventory L m)
    (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    inventory I d v =
      inventory I (d + 1) (leftChild v) +
        inventory I (d + 1) (rightChild v) := by sorry
