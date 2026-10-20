-- Prove2me | Theorems.Thm_CohnElkies_saddleGaussian_fullLine_error_lt_of_central_and_normalized_tails
-- name    : CohnElkies.saddleGaussian_fullLine_error_lt_of_central_and_normalized_tails
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.023852+00:00
-- url     : https://prove2.me/theorems/d2828623-aa6d-46bc-be2f-761cdb9e88a2
-- title:
--   CohnElkies.saddleGaussian_fullLine_error_lt_of_central_and_normalized_tails
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

theorem CohnElkies.saddleGaussian_fullLine_error_lt_of_central_and_normalized_tails
    {ε ℓ u R A κcentral κsource κgaussian : ℝ}
    {F G : ℝ → ℂ}
    (hF : Integrable F) (hG : Integrable G)
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (hcentral :
      ‖∫ T : ℝ in Icc (-R) R, (F T - G T)‖ <
        κcentral * A *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T))
    (hsource :
      Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
        (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) <
          κsource * A)
    (hgaussian :
      Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
        (∫ T : ℝ in saddleGaussianTailSet R, ‖G T‖) <
          κgaussian * A) :
    ‖(∫ T : ℝ, F T) - (∫ T : ℝ, G T)‖ <
      (κcentral + (κsource + κgaussian) /
        Real.sqrt (2 * Real.pi)) * A *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) := by sorry
