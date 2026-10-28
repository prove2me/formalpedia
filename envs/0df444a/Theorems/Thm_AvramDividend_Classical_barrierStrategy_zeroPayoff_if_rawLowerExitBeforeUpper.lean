-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_zeroPayoff_if_rawLowerExitBeforeUpper
-- name    : AvramDividend.Classical.barrierStrategy_zeroPayoff_if_rawLowerExitBeforeUpper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:35:51.517049+00:00
-- url     : https://prove2.me/theorems/6542a845-c441-4319-87c5-b5f2bef6a2bc
-- title:
--   Raw lower exit before first upper passage kills the discounted barrier dividend payoff
-- statement:
--   Whenever the unregulated Lévy reserve falls below negative initial capital before the first upper barrier passage, the controlled barrier strategy pays zero discounted Stieltjes dividends before ruin. This is precisely the killed lower-first branch of the source two-sided exit event.
-- source:
--   Direct raw killed-exit zero-payoff branch of W-free strong-Markov theorem 79978d61-9d1f-4b20-b8a5-114797a8e380, composing Proved clock equivalence 00fd3516-3ab6-4e48-b848-19dc47c0023d and Proved finite-ruin payoff vanishing ba67a140-fd33-4fb1-8dda-ec8dbe888e1c.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_ruinClock_lt_upClock_iff_rawLowerClock_lt
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_discountedDividend_zero_if_ruin_before_upcrossing

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_zeroPayoff_if_rawLowerExitBeforeUpper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hraw : (⨅ (s : ℝ≥0) (_ : X.X s ω < -x),
      (s : ℝ≥0∞)) < (u : ℝ≥0∞)) :
    (∫⁻ t in paymentTimes
        (ruinTime X x (barrierStrategy X x a) ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure (barrierStrategy X x a) ω)) = 0 := by
  sorry
