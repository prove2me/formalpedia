-- Prove2me | Theorems.Thm_CohnElkies_upperGammaVarianceDensity_pointwise_bounds
-- name    : CohnElkies.upperGammaVarianceDensity_pointwise_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:55.583848+00:00
-- url     : https://prove2.me/theorems/223cdfb6-a03b-48da-ae93-a1febc1b51af
-- title:
--   CohnElkies.upperGammaVarianceDensity_pointwise_bounds
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

theorem CohnElkies.upperGammaVarianceDensity_pointwise_bounds
    {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    (ℓ / 2) * Real.exp (-η * a) ≤
      a ^ 2 * upperGammaMeasureDensity ℓ η a ∧
    a ^ 2 * upperGammaMeasureDensity ℓ η a ≤
      (a + ℓ / 2) * Real.exp (-η * a) := by sorry
