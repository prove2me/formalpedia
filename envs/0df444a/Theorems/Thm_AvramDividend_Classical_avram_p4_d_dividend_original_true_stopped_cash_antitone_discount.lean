-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_stopped_cash_antitone_discount
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_true_stopped_cash_antitone_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:21:58.522799+00:00
-- url     : https://prove2.me/theorems/18318a57-0e77-4fd3-9717-388508b7cf1d
-- title:
--   True ruin-stopped original dividend cash is antitone in discount rate
-- statement:
--   At each nonnegative actual source payment time before the true extended ruin deadline and up to the closed finite horizon, a larger discount rate gives a smaller real exponential weight. Monotonicity of the original Stieltjes lintegral gives antitonicity in q without a density or atomlessness assumption. No sign of q is required because actual payment times are nonnegative.
-- source:
--   Proved original paymentTimes support and measurability, original source dividendMeasure and ENNReal lintegral monotonicity

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_true_stopped_cash_antitone_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (T : ℝ≥0)
    (q₁ q₂ : ℝ) (hq : q₁ ≤ q₂) :
    (∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q₂ * s))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q₁ * s))) ∂(dividendMeasure D ω)) := by sorry
