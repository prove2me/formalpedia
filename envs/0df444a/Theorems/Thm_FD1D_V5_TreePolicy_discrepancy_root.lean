-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_discrepancy_root
-- name    : FD1D.V5.TreePolicy.discrepancy_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:36:02.829092+00:00
-- url     : https://prove2.me/theorems/4e875b93-5083-57a9-8b53-d7ec3eeea32f
-- title:
--   Tree Policy: discrepancy root
-- statement:
--   The Tree Policy construction uses the discrepancy root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L143-L146
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L143-L146

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.discrepancy_root (I : AggregatedInventory L m) {a : ℝ}
    (_ha : 0 < a) (hm : 0 < m) :
    discrepancy I a 0 dyadicRoot = 0 := by sorry
