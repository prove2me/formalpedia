-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_deterministic_aggregate_estimate
-- name    : FD1D.V5.TreePolicy.deterministic_aggregate_estimate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:53:04.119221+00:00
-- url     : https://prove2.me/theorems/3d06e93f-ab37-53ff-8d37-61e2e2b98d80
-- title:
--   Tree Policy: deterministic aggregate estimate
-- statement:
--   The deterministic aggregate estimate from Proposition 4.3 of the manuscript:
--   `D ≥ a H_L / 1000 + G / (1000 a) - 501 a / (1000 m²)`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L622-L772
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L622-L772

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.deterministic_aggregate_estimate
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    restoringDrift I a ≥
      a / 1000 * hazardEnergy (rate I a) L +
        transportEnergy I a / (1000 * a) -
        501 * a / (1000 * (m : ℝ) ^ 2) := by sorry
