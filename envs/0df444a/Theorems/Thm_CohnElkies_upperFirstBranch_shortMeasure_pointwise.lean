-- Prove2me | Theorems.Thm_CohnElkies_upperFirstBranch_shortMeasure_pointwise
-- name    : CohnElkies.upperFirstBranch_shortMeasure_pointwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.260927+00:00
-- url     : https://prove2.me/theorems/a40e2f08-0497-4499-af09-fb5a0dd1fc5d
-- title:
--   CohnElkies.upperFirstBranch_shortMeasure_pointwise
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology

theorem CohnElkies.upperFirstBranch_shortMeasure_pointwise
    {ε ℓ u a : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (ha : 0 < a)
    (hulower : -1 ≤ u)
    (huupper : u ≤ 1 + ε / 2)
    (hmargin : 0 ≤ shortMargin ε a) :
    ℓ * (-shortShellDensity ε a) * Real.cosh (u * a) ≤
      (1 - 4 * ε) *
        upperGammaMeasureDensity ℓ (1 + u) a := by sorry
