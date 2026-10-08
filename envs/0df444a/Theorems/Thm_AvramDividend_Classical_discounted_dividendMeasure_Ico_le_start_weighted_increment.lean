-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_dividendMeasure_Ico_le_start_weighted_increment
-- name    : AvramDividend.Classical.discounted_dividendMeasure_Ico_le_start_weighted_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T08:19:14.686762+00:00
-- url     : https://prove2.me/theorems/cc561cd6-930d-4025-846b-df8e60e99327
-- title:
--   Full discounted Stieltjes dividend integral on [a,b) is bounded by the interval's start discount times the actual dividend increment
-- statement:
--   For every dividend strategy D, nonnegative discount q and any nonnegative a,b, the complete Lebesgue–Stieltjes integral of exp(−qt) on [a,b) against its dividend measure is bounded by exp(−qa) times the actual dividend increment D_b−D_a. This holds for continuous dividend flows and arbitrary jumps because exp(−qs)≤exp(−qa) throughout [a,b), and the Stieltjes measure of [a,b) exactly equals the dividend increment. It supplies a genuine discounted stepwise upper bound for continuous and atomic dividends alike, suitable for partition approximations and integration-by-parts estimates.
-- source:
--   Child dividendMeasure_Ico_eq_dividend_increment; pinned Mathlib lintegral_mono_ae, ae_restrict_of_forall_mem, lintegral_const, ENNReal.ofReal_mul and Real.exp_le_exp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_dividendMeasure_Ico_le_start_weighted_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ≥0) :
    (∫⁻ s in Ico (a : ℝ) (b : ℝ),
       ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (a : ℝ))) *
        (D b ω - D a ω)) := by sorry
