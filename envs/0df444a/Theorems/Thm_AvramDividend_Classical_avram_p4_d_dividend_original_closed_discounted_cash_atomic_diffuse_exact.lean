-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_discounted_cash_atomic_diffuse_exact
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_closed_discounted_cash_atomic_diffuse_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T22:11:13.482252+00:00
-- url     : https://prove2.me/theorems/0b22cdad-7a4d-4ad0-ac06-c946134eabd6
-- title:
--   Exact original stopped discounted dividend Cash splits into atom and diffuse integrals
-- statement:
--   For the actual adapted original dividend strategy and its pre-ruin paymentTimes intersected with the closed horizon Iic T, the entire discounted ENNReal Stieltjes dividend Cash is the sum of the integral against all positive-mass singleton rightpayment times and its complementary atomless restriction. This equality holds before ENNReal.toReal and therefore cannot discard time-zero or terminal-time masses or any singular-continuous component.
-- source:
--   Accepted full original atomic-diffuse measure identity e0edcc7b, pinned Mathlib Measure.restrict_add and lintegral_add_measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_pathwise_atomic_diffuse_measure_sum

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_closed_discounted_cash_atomic_diffuse_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0) (q : ℝ) :
    ∀ ω : Ω,
      (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) =
      (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂
          (dividendMeasure D ω).restrict
            {t : ℝ | 0 < dividendMeasure D ω {t}}) +
      (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂
          (dividendMeasure D ω).restrict
            {t : ℝ | ¬0 < dividendMeasure D ω {t}}) := by sorry
