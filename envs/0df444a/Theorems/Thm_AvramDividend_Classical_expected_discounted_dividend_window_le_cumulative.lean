-- Prove2me | Theorems.Thm_AvramDividend_Classical_expected_discounted_dividend_window_le_cumulative
-- name    : AvramDividend.Classical.expected_discounted_dividend_window_le_cumulative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:06:40.796039+00:00
-- url     : https://prove2.me/theorems/8842e40f-98f5-4b0b-9055-26bf62a28b9e
-- title:
--   Expected stopped discounted dividend payout bounded by expected cumulative dividends
-- statement:
--   A direct expectation-level domination of the original stopped Stieltjes dividend payoff by the time-(T+1) cumulative dividend. The inequality needs no integrability assumptions because both sides are ENNReal-valued. It provides a quantitative localising domination for the expected stochastic-verification step.

import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_lintegral_le_measure
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Mathlib.Tactic.NormNum

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.expected_discounted_dividend_window_le_cumulative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞) (T : ℝ≥0) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ∫⁻ ω, ENNReal.ofReal (D (T + 1) ω) ∂P := by sorry
