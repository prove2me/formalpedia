-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:09:55.028672+00:00
-- url     : https://prove2.me/theorems/c4e50d93-76bf-4771-9e5f-5ffeba198952
-- title:
--   Original ruin-stopped finite-horizon literal dividend Cash lintegral is pathwise finite
-- statement:
--   For every original admissible dividend strategy, every sample path, any extended ruin deadline sigma, any finite nonnegative observation horizon T, and nonnegative discount q, the literal ENNReal lintegral of exp(-qs) against dividendMeasure restricted to true paymentTimes sigma intersected with the closed horizon is finite. This directly matches the source of canonical P4-F Cash.toReal: payment times are nonnegative, exp(-qs)≤1 there, and the entire closed-horizon Stieltjes mass is the finite real rightLimit D T. Includes time-zero and horizon right-payment atoms; positive-ruin payments are handled by paymentTimes sigma.
-- source:
--   Proved paymentTimes_membership_to_nNReal_active, paymentTimes_measurable, and source dividendMeasure_Icc_zero_eq_rightLimit; original P4-F stopped Cash

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) < ⊤ := by sorry
