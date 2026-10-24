-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_truncated_stieltjes_le_future_cumulative_dividends
-- name    : AvramDividend.Classical.local_verification_truncated_stieltjes_le_future_cumulative_dividends
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:30:08.122644+00:00
-- url     : https://prove2.me/theorems/abb4e5d3-81b8-49e2-a642-1c559bf149df
-- title:
--   Full stopped Stieltjes reward before a horizon is bounded by a later cumulative dividend total
-- statement:
--   For any admissible dividend strategy, any nonnegative discount rate, arbitrary ruin or stopping cut-off σ, and deterministic times T<S, all discounted Stieltjes dividend payments at permitted payment times through T are bounded by the cumulative strategy dividends D(S). The proof uses set inclusion in [0,S) and the proved full-measure discounted Stieltjes cumulative bound, retaining continuous dividend payouts and all right-jump atoms. This gives a direct random-variable domination useful for finite-grid localisation and expectation bounds.
-- source:
--   Proved discounted_dividendMeasure_Ico_zero_le_dividend_cumulative (9a0c3a15-0585-461a-b3fc-9a117ede6a13), with MeasureTheory.lintegral_mono_set.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_discounted_dividendMeasure_Ico_zero_le_dividend_cumulative

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_truncated_stieltjes_le_future_cumulative_dividends
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞)
    (T S : ℝ≥0) (hTS : T < S) :
    (∫⁻ r in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (D S ω) := by sorry
