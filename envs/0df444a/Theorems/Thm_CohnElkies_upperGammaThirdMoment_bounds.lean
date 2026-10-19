-- Prove2me | Theorems.Thm_CohnElkies_upperGammaThirdMoment_bounds
-- name    : CohnElkies.upperGammaThirdMoment_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:55.583848+00:00
-- url     : https://prove2.me/theorems/5a02668a-ce70-4f06-bb08-6ae15abcc555
-- title:
--   CohnElkies.upperGammaThirdMoment_bounds
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

theorem CohnElkies.upperGammaThirdMoment_bounds
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) :
    1 / (2 * η ^ 2) ≤ upperGammaThirdMoment ℓ η ∧
      upperGammaThirdMoment ℓ η ≤
        1 / (2 * η ^ 2) + 2 / (ℓ * η ^ 3) := by sorry
