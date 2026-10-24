-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_dividend_window_le_cumulative
-- name    : AvramDividend.Classical.discounted_dividend_window_le_cumulative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:06:59.679406+00:00
-- url     : https://prove2.me/theorems/8faf8c3a-05a6-4de1-97eb-11f4056ec333
-- title:
--   Stopped discounted dividend payout bounded by finite cumulative dividends
-- statement:
--   For any admissible-form dividend strategy (its monotonicity and finite values suffice), discounted Stieltjes rewards on payment times through T are at most cumulative D(T+1). This combines the verified exponential-discount mass domination with the exact Stieltjes interval mass identity, and includes continuous as well as atomic dividend payments.

import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_lintegral_le_measure
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Mathlib.Tactic.NormNum

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.discounted_dividend_window_le_cumulative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0)
    (ω : Ω) :
    (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤ ENNReal.ofReal (D (T + 1) ω) := by sorry
