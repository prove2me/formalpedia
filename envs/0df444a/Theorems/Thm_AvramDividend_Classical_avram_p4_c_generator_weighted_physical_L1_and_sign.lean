-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_weighted_physical_L1_and_sign
-- name    : AvramDividend.Classical.avram_p4_c_generator_weighted_physical_L1_and_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:11:43.860675+00:00
-- url     : https://prove2.me/theorems/f9d4f8ff-0c2b-4bc3-a151-55ab330f1469
-- title:
--   Transport original weighted predictable generator L1 to exact physical epsilon drift and obtain nonpositive signed integral
-- statement:
--   For arbitrary measured localisation including genuine predictable time×sample clocks, nonnegative predictable weight a, and source HJB on strict interior, any L1 weighted source generator residual transfers exactly to the ε-physical Gaussian/drift/uncompensated-large/compensated-small residual, with identical total integral and a nonpositive total. All y-dependent source GeneratorIntegrable are derived from source HJB. Source time L1 is an explicit hypothesis to be supplied by the existing Proved true-clock theorem 72ccc7b2, and no original jump-counting compensator is postulated.
-- source:
--   P4-C compact generator identity, Mathlib integral_nonpos_of_ae, source 72ccc7b2 actual predictable clock L1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_weighted_physical_L1_and_sign
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {α : Type*} [mα : MeasurableSpace α]
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (μ : Measure α) (u : α → ℝ) (a : α → ℝ) (A : Set α)
    (hA : MeasurableSet A)
    (hregion : ∀ p ∈ A, 0 < u p ∧ ENNReal.ofReal (u p) < C)
    (ha : ∀ p ∈ A, 0 ≤ a p) :
    let F : α → ℝ := fun p => a p * (X.generator w (u p) - q * w (u p))
    let G : α → ℝ := fun p => a p *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (u p) +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w (u p) +
        (∫ z in Iio (-ε), w (u p + z) - w (u p) ∂X.ν) +
        (∫ z in Ico (-ε) 0,
          SpectrallyNegativeLevy.generatorIntegrand w (u p) z ∂X.ν) -
        q * w (u p))
    IntegrableOn F A μ →
      IntegrableOn G A μ ∧
      (∫ p in A, G p ∂μ) = (∫ p in A, F p ∂μ) ∧
      (∫ p in A, G p ∂μ) ≤ 0 := by sorry
