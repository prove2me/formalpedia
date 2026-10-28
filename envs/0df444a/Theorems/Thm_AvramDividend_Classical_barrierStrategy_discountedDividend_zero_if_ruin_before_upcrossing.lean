-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_discountedDividend_zero_if_ruin_before_upcrossing
-- name    : AvramDividend.Classical.barrierStrategy_discountedDividend_zero_if_ruin_before_upcrossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:34:23.310117+00:00
-- url     : https://prove2.me/theorems/ba67a140-fd33-4fb1-8dda-ec8dbe888e1c
-- title:
--   Vanishing discounted barrier dividends when ruin precedes first upper passage
-- statement:
--   If controlled ruin occurs no later than a finite first passage to the dividend barrier, every payment time is inside the zero-Stieltjes-mass closed window, so the entire discounted dividend payoff vanishes pathwise. This is the ruin-before-passage branch of the root-connected strong-Markov barrier valuation split.
-- source:
--   Root-connected canonical strong-Markov theorem 79978d61-9d1f-4b20-b8a5-114797a8e380. Uses the previously proved closed-window Stieltjes dividend zero theorem 4396ddd6-6981-42c6-9f15-733157b72a22 and measure-zero lintegral.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_through_firstUpcrossing

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_discountedDividend_zero_if_ruin_before_upcrossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x a : ℝ)
    (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hruin : ruinTime X x (barrierStrategy X x a) ω ≤ (u : ℝ≥0∞)) :
    (∫⁻ t in paymentTimes (ruinTime X x (barrierStrategy X x a) ω),
       ENNReal.ofReal (Real.exp (-(q * t)))
       ∂(dividendMeasure (barrierStrategy X x a) ω)) = 0 := by
  sorry
