-- Prove2me | Theorems.Thm_CohnElkies_upperGammaVariance_bounds
-- name    : CohnElkies.upperGammaVariance_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:55.583848+00:00
-- url     : https://prove2.me/theorems/22db76f8-8744-404f-a075-fa38053a039f
-- title:
--   CohnElkies.upperGammaVariance_bounds
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

theorem CohnElkies.upperGammaVariance_bounds
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) :
    1 / (2 * η) ≤ upperGammaVariance ℓ η ∧
      upperGammaVariance ℓ η ≤
        1 / (2 * η) + 1 / (ℓ * η ^ 2) := by sorry
