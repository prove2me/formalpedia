-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_discountedPayoff_zero_outside_rawTwoSidedExit
-- name    : AvramDividend.Classical.barrierStrategy_discountedPayoff_zero_outside_rawTwoSidedExit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:05:31.517521+00:00
-- url     : https://prove2.me/theorems/576fffea-9646-44c5-a64b-0ac4b97b4bcc
-- title:
--   Stopped barrier dividends vanish unless the raw upper exit wins against ruin
-- statement:
--   For a positive barrier and nonnegative initial surplus below it, the actual pre-ruin Stieltjes dividend reward is zero on every sample path where the raw strict upper first-exit does not precede the strict lower ruin exit, including equality and infinite-clock cases. This upgrades the Proved zero-payoff theorem phrased using controlled ruin to the exact two-sided upper-before-lower event in the standing-only strong-Markov dividend-value identity.
-- source:
--   The proved barrierStrategy_discountedPayoff_zero_outside_controlledUpExit and the exact raw-versus-controlled first-exit event equivalence barrierStrategy_upExit_before_controlledRuin_iff_rawExit; needed to restrict the pathwise payoff integral to the killed raw two-sided exit event in dividendValue_barrierStrategy_upExit_split_of_standing.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_upExit_before_controlledRuin_iff_rawExit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_discountedPayoff_zero_outside_controlledUpExit
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_discountedPayoff_zero_outside_rawTwoSidedExit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x a : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω)
    (hraw : ¬
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) <
        (⨅ (s : ℝ≥0) (_ : X.X s ω < -x), (s : ℝ≥0∞))) :
    (∫⁻ t in paymentTimes (ruinTime X x (barrierStrategy X x a) ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (barrierStrategy X x a) ω)) = 0 := by sorry
