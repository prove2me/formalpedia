-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_stopped_bounded_signed_stieltjes_integrableOn
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_true_stopped_bounded_signed_stieltjes_integrableOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:31:35.644044+00:00
-- url     : https://prove2.me/theorems/617614f3-804f-4c2a-8a86-2846f12ae90f
-- title:
--   Bounded signed original stopped dividend residual kernels are pathwise Stieltjes-integrable
-- statement:
--   On an original admissible dividend path and genuine ruin-stopped closed finite-horizon payment domain, any real-valued almost-everywhere strongly measurable integrand with an almost-everywhere finite uniform norm bound is integrable against the original dividend Stieltjes measure. The measure of the full set is finite by the source rightLimit identity. This gives a source-faithful sufficient condition for signed dividend-control residual integrals, covering singular continuous and atomic mass without density assumptions.
-- source:
--   Original source paymentTimes support and dividendMeasure_Icc_zero_eq_rightLimit; Mathlib IntegrableOn.of_bound

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_true_stopped_bounded_signed_stieltjes_integrableOn
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f
      ((dividendMeasure D ω).restrict (paymentTimes σ ∩ Iic (T : ℝ))))
    (C : ℝ)
    (hC : ∀ᵐ u ∂(dividendMeasure D ω).restrict (paymentTimes σ ∩ Iic (T : ℝ)),
      ‖f u‖ ≤ C) :
    IntegrableOn f (paymentTimes σ ∩ Iic (T : ℝ)) (dividendMeasure D ω) := by sorry
