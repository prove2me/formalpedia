-- Prove2me | Theorems.Thm_AvramDividend_Classical_truncated_dividend_payoff_measurable
-- name    : AvramDividend.Classical.truncated_dividend_payoff_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T09:41:18.143019+00:00
-- url     : https://prove2.me/theorems/c10d5702-c15b-4a73-8ffe-4d7cda5582f0
-- title:
--   Truncated discounted Stieltjes dividend payout is a measurable random variable
-- statement:
--   For any left-continuous adapted nondecreasing dividend process D and Lévy process X, the truncated payout ω↦∫_{paymentTimes(σ(ω))∩(−∞,n]} exp(−qt) dD(ω)(t) is measurable for every natural horizon n. This is a major technical obligation for passing from the open BV/UBV truncated stochastic bounds to the full expected dividendValue via monotone convergence. The underlying ruinTime measurability and rightLimit measurability are already proved, and interval-mass measurability of dividendMeasure is available. The main remaining step is measurable random Stieltjes integral construction.
-- source:
--   Proved ruinTime_measurable, dividendStrategy_rightLimit_measurable, dividendMeasure_Ioc_measurable, paymentTimes_measurable; Mathlib measurable-lintegral kernel infrastructure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.truncated_dividend_payoff_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    ∀ n : ℕ, Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
