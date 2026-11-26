-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_leaf_deletionMass_pos_of_count_pos
-- name    : FD1D.V5.TreePolicy.leaf_deletionMass_pos_of_count_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:52:09.268463+00:00
-- url     : https://prove2.me/theorems/c0c8ae82-c5aa-45bb-9d28-2f8a28c6138b
-- title:
--   Tree Policy: leaf deletion Mass pos of count pos
-- statement:
--   The Tree Policy construction uses the leaf deletion Mass pos of count pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L355-L361
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L355-L361

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.leaf_deletionMass_pos_of_count_pos
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) (v : DyadicNode L)
    (hv : 0 < I.count L v) :
    0 < deletionMass I a L v := by sorry
