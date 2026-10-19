-- Prove2me | Theorems.Thm_CohnElkies_upperGammaThirdMomentDensity_pointwise_bounds
-- name    : CohnElkies.upperGammaThirdMomentDensity_pointwise_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:55.583848+00:00
-- url     : https://prove2.me/theorems/1549f254-760f-4e51-9133-963e7b3e099d
-- title:
--   CohnElkies.upperGammaThirdMomentDensity_pointwise_bounds
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

theorem CohnElkies.upperGammaThirdMomentDensity_pointwise_bounds
    {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    (ℓ / 2) * a * Real.exp (-η * a) ≤
      a ^ 3 * upperGammaMeasureDensity ℓ η a ∧
    a ^ 3 * upperGammaMeasureDensity ℓ η a ≤
      (a ^ 2 + (ℓ / 2) * a) *
        Real.exp (-η * a) := by sorry
