-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_discrepancy_le_half
-- name    : FD1D.V5.TreePolicy.discrepancy_le_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:36:23.268798+00:00
-- url     : https://prove2.me/theorems/47b04195-b7b3-45d9-97b8-ed627b1a7122
-- title:
--   Tree Policy: discrepancy le half
-- statement:
--   The Tree Policy construction uses the discrepancy le half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L305-L309
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L305-L309

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.discrepancy_le_half (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    discrepancy I a d v ≤ rate I a d v / 2 := by sorry
