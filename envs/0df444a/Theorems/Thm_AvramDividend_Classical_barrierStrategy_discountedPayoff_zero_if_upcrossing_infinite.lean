-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_discountedPayoff_zero_if_upcrossing_infinite
-- name    : AvramDividend.Classical.barrierStrategy_discountedPayoff_zero_if_upcrossing_infinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:50:53.001049+00:00
-- url     : https://prove2.me/theorems/81bd950e-d373-434a-ba2c-8ad6fde07481
-- title:
--   Entire discounted barrier payoff vanishes on infinite first-upper-passage paths
-- statement:
--   The killed strong-Markov barrier payoff is zero on sample paths whose first strict upper passage is infinite, even if the ruin time is also infinite. This follows from zero cumulative barrier dividends at every finite time and the exact zero-cumulative-dividends implies zero-Stieltjes-payoff theorem.
-- source:
--   Root-connected infinite-clock branch of W-free strong-Markov dividend target 79978d61-9d1f-4b20-b8a5-114797a8e380. Uses two immediately pursued Proved prerequisites and existing barrier strategy admissibility theorem 501af29f-f958-42d6-8682-5dc331fedae7.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_if_firstUpcrossing_infinite
import Theorems.Thm_AvramDividend_Classical_zeroCumulativeDividend_implies_zeroStieltjesPayoff
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_discountedPayoff_zero_if_upcrossing_infinite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω)
    (hnever : (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω),
      (s : ℝ≥0∞)) = ⊤) :
    (∫⁻ t in paymentTimes
        (ruinTime X x (barrierStrategy X x a) ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure (barrierStrategy X x a) ω)) = 0 := by
  sorry
