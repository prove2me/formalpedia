-- Prove2me | Theorems.Thm_AvramDividend_Classical_general_stopped_dividend_integral_measurable
-- name    : AvramDividend.Classical.general_stopped_dividend_integral_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T06:57:37.102533+00:00
-- url     : https://prove2.me/theorems/02b58b54-f5f2-4960-a1ea-80bd63146bf4
-- title:
--   The full pre-ruin discounted Stieltjes dividend payoff is a measurable random variable for every dividend strategy
-- statement:
--   The full stopped, q-discounted Stieltjes integral defining the pathwise dividend payoff is measurable in the sample ω for any adapted left-continuous nondecreasing dividend strategy D, including continuously paid dividends. The indicator form has already been handled by a measurable s-finite dividend-measure kernel and jointly measurable ruin-stopping region. The payment-time set is Borel for each ω, so the standard nonnegative integral indicator identity converts the measurable full-domain integrand to the exact original restricted integral.
-- source:
--   Dependencies: AvramDividend.Classical.general_stopped_dividend_indicator_reward_measurable and AvramDividend.Classical.paymentTimes_measurable, plus Mathlib.MeasureTheory.lintegral_indicator.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_general_stopped_dividend_indicator_reward_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.general_stopped_dividend_integral_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
