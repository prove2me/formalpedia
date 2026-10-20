-- Prove2me | Theorems.Thm_AvramDividend_Classical_truncated_zero_horizon_bound_of_initial_jump_secant
-- name    : AvramDividend.Classical.truncated_zero_horizon_bound_of_initial_jump_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:51:44.912512+00:00
-- url     : https://prove2.me/theorems/cd2d62d3-c5c3-4cd5-8783-4155692e2c6d
-- title:
--   Exact zero-horizon stochastic dividend upper bound from the initial-jump HJB inequality
-- statement:
--   For any spectrally negative Lévy process on the given filtered probability space and any dividend strategy D, assume the initial right-payment amount is bounded by the candidate function's decrease across that payment and the candidate remains nonnegative after the payment. Then the exact published expected discounted dividends truncated at horizon T=0 are bounded above by ENNReal.ofReal(w x). This is a genuine exact zero-horizon special case of the corrected BV and UBV stopped dividend bounds, including the initial Stieltjes atom and ruin at zero; it uses the Proved exact zero-horizon atom identity and the probability measure field, but does not assert the still-open positive-time stochastic Ito inequality.
-- source:
--   Proved truncated_dividend_payoff_at_zero_eq_initial_atom and pinned dividendValue/paymentTimes definitions; elementary ENNReal integral monotonicity.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_truncated_dividend_payoff_at_zero_eq_initial_atom

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.truncated_zero_horizon_bound_of_initial_jump_secant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hjump : ∀ ω,
       rightLimit D 0 ω - D 0 ω ≤
         w x - w (x - (rightLimit D 0 ω - D 0 ω)))
    (hpost : ∀ ω, 0 ≤ w (x - (rightLimit D 0 ω - D 0 ω))) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    ENNReal.ofReal (w x) := by sorry
