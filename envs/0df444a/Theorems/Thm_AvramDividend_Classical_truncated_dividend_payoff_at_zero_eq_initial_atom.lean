-- Prove2me | Theorems.Thm_AvramDividend_Classical_truncated_dividend_payoff_at_zero_eq_initial_atom
-- name    : AvramDividend.Classical.truncated_dividend_payoff_at_zero_eq_initial_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T15:58:27.675879+00:00
-- url     : https://prove2.me/theorems/50183965-497e-4b6a-9601-a1cc826ac588
-- title:
--   Exact zero-horizon truncated dividend payoff is the initial Stieltjes atom
-- statement:
--   For any dividend strategy and any possibly zero or infinite ruin time, restricting the formally defined discounted Stieltjes dividend reward to paymentTimes intersected with (-∞,0] leaves precisely the time-zero payment. The reward is ENNReal.ofReal(rightLimit D at 0 minus D at 0), independent of q and the ruin time. This detects the missing initial-capital and w(x) boundary hypotheses in the published BV/UBV stochastic upper-bound statements.
-- source:
--   Pinned Formalpedia exact dividendMeasure, paymentTimes and dividendMeasure_singleton_eq_rightLimit_sub; pinned Mathlib MeasureTheory.lintegral_singleton.

import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.truncated_dividend_payoff_at_zero_eq_initial_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (σ : ℝ≥0∞) (ω : Ω) :
    (∫⁻ t in paymentTimes σ ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    ENNReal.ofReal (rightLimit D 0 ω - D 0 ω) := by sorry
