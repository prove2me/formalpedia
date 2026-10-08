-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_dividendMeasure_Ico_zero_le_dividend_cumulative
-- name    : AvramDividend.Classical.discounted_dividendMeasure_Ico_zero_le_dividend_cumulative
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T08:16:58.37288+00:00
-- url     : https://prove2.me/theorems/9a0c3a15-0585-461a-b3fc-9a117ede6a13
-- title:
--   The complete discounted Stieltjes dividend integral on [0,t) is bounded by cumulative dividends D(t)
-- statement:
--   For any actual dividend strategy D, path ω, nonnegative discount q and horizon t, the full discounted Lebesgue–Stieltjes dividend integral over [0,t), including both continuous dividend flows and right dividend jumps, is at most ENNReal.ofReal(D_t). Indeed exp(−q s)≤1 for s≥0, and the actual dividendMeasure of [0,t) equals the path increment D_t−D_0=D_t. This builds a concrete all-payout bound that is independent of the HJB generator and avoids mistakenly treating continuous dividends as atomic.
-- source:
--   Child dividendMeasure_Ico_zero_eq_dividendValue; pinned Mathlib lintegral_mono_ae, ae_restrict_of_forall_mem, lintegral_one and Real.exp_le_one_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_dividendMeasure_Ico_zero_le_dividend_cumulative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (t : ℝ≥0) :
    (∫⁻ s in Ico (0 : ℝ) (t : ℝ),
       ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (D t ω) := by sorry
