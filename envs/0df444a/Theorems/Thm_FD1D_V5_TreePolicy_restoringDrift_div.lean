-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_restoringDrift_div
-- name    : FD1D.V5.TreePolicy.restoringDrift_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:38:06.575419+00:00
-- url     : https://prove2.me/theorems/0a9143b6-d942-403c-9447-f16aecad17d6
-- title:
--   Tree Policy: restoring Drift div
-- statement:
--   The restoring drift is `a` times the nonroot weighted `t Z` sum.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L573-L586
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L573-L586

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.restoringDrift_div
    (I : AggregatedInventory L m) {a : ℝ} (ha : 0 < a) :
    restoringDrift I a / a =
      nonrootWeightedSum
        (fun d v => discrepancy I a d v * regularizedMass I a d v) L := by sorry
