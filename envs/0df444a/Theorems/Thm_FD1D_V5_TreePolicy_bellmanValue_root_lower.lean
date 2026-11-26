-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_bellmanValue_root_lower
-- name    : FD1D.V5.TreePolicy.bellmanValue_root_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:38:02.590617+00:00
-- url     : https://prove2.me/theorems/8aaab459-a16c-4106-b217-22ead1244af4
-- title:
--   Tree Policy: bellman Value root lower
-- statement:
--   The Tree Policy construction uses the bellman Value root lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L602-L616
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L602-L616

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.bellmanValue_root_lower
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    -(1 / (2 * (m : ℝ) ^ 2)) ≤
      bellmanValue I a 0 dyadicRoot := by sorry
