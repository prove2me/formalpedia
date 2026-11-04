-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_true_clock_finite_of_lintegral_transfer
-- name    : AvramDividend.Classical.avram_p4_c_generator_true_clock_finite_of_lintegral_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:50:08.280855+00:00
-- url     : https://prove2.me/theorems/30a4105b-eb88-4808-bff0-cd13f9301c25
-- title:
--   Original predictable clock measure finite under exact physical lintegral transfer from finite product clock
-- statement:
--   From the original true predictable clock's equality of all nonnegative measurable lintegrals with the finite physical time-product source measure, apply it to the constant-one integrand and infer finite total measure. The source product clock's finiteness is an explicit premise, to be discharged using the finite horizon T and the original process probability hypotheses; no hidden finite measure assumption is made. This is useful for continuous and payoff L1 on the physical clock.
-- source:
--   Original true-clock lintegral equality hμ from c254b492 and Mathlib lintegral_one/isFiniteMeasure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_true_clock_finite_of_lintegral_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : ∀ f : (ℝ≥0 × Ω) → ℝ≥0∞,
      Measurable[𝓕.rightCont.predictable] f →
      (∫⁻ p, f p ∂μ) =
        (∫⁻ p, f p ∂((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)))
    (hsourceFinite :
      (((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) Set.univ) < ⊤) :
    IsFiniteMeasure μ := by sorry
