-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_discounted_dividend_payout_integrable_of_cumulative_integrable
-- name    : AvramDividend.Classical.stopped_discounted_dividend_payout_integrable_of_cumulative_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:57:24.56705+00:00
-- url     : https://prove2.me/theorems/d1cfb4e4-ef79-43e4-8f1b-da09c22d022f
-- title:
--   Integrability of complete stopped Stieltjes dividend payouts under a cumulative moment bound
-- statement:
--   At any finite real horizon T and nonnegative discount rate, the total discounted Stieltjes payout before ruin is integrable if cumulative dividends D(T+1) have an integrable nonnegative envelope. First use the independently proved arbitrary-real-horizon stopped dividend payoff measurability, then dominate the full stopped payment integral by ENNReal.ofReal(D(T+1)), transfer toReal monotonicity and invoke Integrable.mono. The theorem is a direct expectation/localisation input to capped bounded- and unbounded-variation stochastic verification, retaining the continuous Stieltjes and right-jump dividend components.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_discounted_dividend_window_le_cumulative
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_dividend_payout_measurable_of_strategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stopped_discounted_dividend_payout_integrable_of_cumulative_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0)
    (hDI : Integrable (fun ω : Ω =>
      (ENNReal.ofReal (D (T + 1) ω)).toReal) P) :
    Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P := by sorry
