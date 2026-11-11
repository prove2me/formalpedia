-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_finite_jump_generator_lower
-- name    : AvramDividend.Classical.avram_mix_fin26_finite_jump_generator_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:28:54.95494+00:00
-- url     : https://prove2.me/theorems/d55f169f-6ae4-43d3-a0fb-7ed68ed584c5
-- title:
--   Finite-intensity spectrally negative jumps have generator contribution at least minus intensity times reward
-- statement:
--   For the original spectrally negative Lévy generator with finite negative-mark intensity λ, if w is nonnegative at all landing reserves not exceeding y, w'(y)≥0, and its generator integrand is integrable, then the entire compensated negative-jump generator contribution is bounded below by -λ w(y). Negative compensation and finite mark intensity make this estimate valid without requiring first absolute moments of unbounded large marks. This supplies a local HJB derivative estimate for finite-mixed Gaussian processes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_negative_jump_generator_kernel_lower
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin26_finite_jump_generator_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y : ℝ)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hGenerator : X.GeneratorIntegrable w y)
    (hReward : ∀ t : ℝ, t ≤ y → 0 ≤ w t)
    (hDeriv : 0 ≤ deriv w y) :
    -((X.ν (Iio (0 : ℝ))).toReal) * w y ≤
      ∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν := by sorry
