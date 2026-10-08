-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_dividendMeasure_Ico_ge_end_weighted_increment
-- name    : AvramDividend.Classical.discounted_dividendMeasure_Ico_ge_end_weighted_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T08:22:07.899404+00:00
-- url     : https://prove2.me/theorems/46bf51b3-7e3b-471b-b401-940f5e0e20b1
-- title:
--   Full discounted Stieltjes dividend integral over [a,b) is at least the end discount times the dividend increment
-- statement:
--   For any actual dividend strategy, nonnegative discount q and times a,b≥0, the discounted Stieltjes dividend integral on [a,b) is bounded below by exp(−qb) times the cumulative dividend increment D_b−D_a. Because exp(−qs)≥exp(−qb) at all s<b, this is the lower companion to the upper bound using exp(−qa). Together these inequalities bracket the full continuous-and-atomic dividend Stieltjes integral by left and right Riemann–Stieltjes sums, which can be used in partition and limiting arguments.
-- source:
--   Child dividendMeasure_Ico_eq_dividend_increment; pinned Mathlib lintegral_mono_ae, ae_restrict_of_forall_mem, lintegral_const, ENNReal.ofReal_mul and Real.exp_le_exp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_dividendMeasure_Ico_ge_end_weighted_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-(q * (b : ℝ))) *
      (D b ω - D a ω)) ≤
    (∫⁻ s in Ico (a : ℝ) (b : ℝ),
       ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by sorry
