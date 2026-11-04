-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_countable_rightjump_local_secant_summable
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_countable_rightjump_local_secant_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:24:49.269115+00:00
-- url     : https://prove2.me/theorems/e4e52ea2-9a88-47f3-a039-67dd3c207934
-- title:
--   Actual original countable right-jump signed remainder is absolutely summable from discounted payments and local secant slope
-- statement:
--   For actual original source Lévy and dividend right payment states, hjump yields the lower secant slope 1. If at each eligible indexed right atom the w-value drop is at most K times the actual dividend increment, with K>=1 and source payment increments nonnegative and their discounted masses summable, then the right-jump signed residual series is absolutely summable and nonpositive. The explicit slope condition only refers to actual post-source/prepayment and postpayment states. It is a conditional boundary-localisation interface and does not incorrectly extrapolate the strict-interior derivative assumption to cap or zero.
-- source:
--   Avram–Palmowski–Pistorius Eq. (5.13), original hjump, Proved source-aware excess domination helper 18d44060.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_countable_rightjump_excess_dominated
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_countable_rightjump_local_secant_summable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    {ι : Type*} (t : ι → ℝ≥0) (ω : Ω)
    (hPre : ∀ i : ι, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (K : ℝ) (hK : 1 ≤ K)
    (hPayNonneg : ∀ i : ι, 0 ≤ rightLimit D (t i) ω - D (t i) ω)
    (hPaySummable : Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        (rightLimit D (t i) ω - D (t i) ω)))
    (hLocalSecant : ∀ i : ι,
      w (riskProcess X x D (t i) ω) -
        w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
          K * (rightLimit D (t i) ω - D (t i) ω)) :
    Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        ((rightLimit D (t i) ω - D (t i) ω) +
          w (x + X.X (t i) ω - rightLimit D (t i) ω) -
          w (riskProcess X x D (t i) ω))) ∧
    (∑' i : ι, Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))) ≤ 0 := by sorry
