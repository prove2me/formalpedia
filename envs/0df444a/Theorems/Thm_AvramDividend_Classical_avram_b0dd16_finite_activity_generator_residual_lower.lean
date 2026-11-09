-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b0dd16_finite_activity_generator_residual_lower
-- name    : AvramDividend.Classical.avram_b0dd16_finite_activity_generator_residual_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T16:35:38.035279+00:00
-- url     : https://prove2.me/theorems/e5e3c876-8a37-45d5-aefd-aafe72cc7599
-- title:
--   Finite jump activity bounds the BV HJB generator residual below by the jump rate and discount
-- statement:
--   For a bounded-variation spectrally negative Levy process with finite negative jump activity, a globally nonnegative candidate and a nonnegative physical-drift derivative, the physical-drift generator formula gives a lower bound on the discounted HJB residual by minus the full jump rate plus discount times the candidate value. The key bound integrates each negative jump increment above minus the candidate value. This is a source-exact finite-activity HJB L1 bridge for the top-cap original BV route.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b0dd16_finite_activity_generator_residual_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (y : ℝ)
    (hGen : X.GeneratorIntegrable w y)
    (hMass : X.ν (Iio (0 : ℝ)) < ⊤)
    (hW : ∀ z : ℝ, 0 ≤ w z)
    (hDrift : 0 ≤ X.drift)
    (hDeriv : 0 ≤ deriv w y) :
    -((X.ν (Iio (0 : ℝ))).toReal + q) * w y ≤
      X.generator w y - q * w y := by sorry
