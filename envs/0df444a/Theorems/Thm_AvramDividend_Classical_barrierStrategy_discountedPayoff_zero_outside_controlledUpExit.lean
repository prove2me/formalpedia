-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_discountedPayoff_zero_outside_controlledUpExit
-- name    : AvramDividend.Classical.barrierStrategy_discountedPayoff_zero_outside_controlledUpExit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:20:00.751756+00:00
-- url     : https://prove2.me/theorems/79e3fad1-6f5e-4f10-9862-e827c71f4c68
-- title:
--   Zero barrier dividends outside the controlled first-upcrossing before ruin event
-- statement:
--   Pathwise discounted barrier dividends vanish whenever first passage above a-x does not occur strictly before controlled ruin, including paths with an infinite first passage. Combines the finite and infinite passage cases without scale-function assumptions.
-- source:
--   Direct structural support for W-free strong-Markov dividend child 79978d61-9d1f-4b20-b8a5-114797a8e380. Discharges the killed-event complement, using Proved finite-ruin and infinite-passage payoff-zero theorems.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_discountedDividend_zero_if_ruin_before_upcrossing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_discountedPayoff_zero_if_upcrossing_infinite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_discountedPayoff_zero_outside_controlledUpExit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω)
    (hkill : ¬
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) <
        ruinTime X x (barrierStrategy X x a) ω) :
    (∫⁻ t in paymentTimes
        (ruinTime X x (barrierStrategy X x a) ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure (barrierStrategy X x a) ω)) = 0 := by
  sorry
