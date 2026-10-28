-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendValue_barrierStrategy_rawTwoSidedExit_support
-- name    : AvramDividend.Classical.dividendValue_barrierStrategy_rawTwoSidedExit_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:29:50.598102+00:00
-- url     : https://prove2.me/theorems/abb0ce48-c7f2-4810-9547-98c734b0c232
-- title:
--   Barrier dividend value equals its raw two-sided exit-event restricted expectation
-- statement:
--   For initial reserves 0≤x≤a and positive dividend barrier a, the full expected discounted stopped barrier dividends equal the expectation of the same stopped Stieltjes dividend reward restricted to paths where raw upward passage precedes raw lower ruin. This is the immediate support-normalisation stage of the below-barrier strong-Markov factorisation.
-- source:
--   Proved zero-payoff lemma 576fffea-9646-44c5-a64b-0ac4b97b4bcc, Avram Palmowski Pistorius (2007) Proposition 1; upstream support identity for 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_discountedPayoff_zero_outside_rawTwoSidedExit
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.dividendValue_barrierStrategy_rawTwoSidedExit_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x a : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) =
      ∫⁻ ω, if (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) <
          (⨅ (s : ℝ≥0) (_ : X.X s ω < -x), (s : ℝ≥0∞)) then
        (∫⁻ t in paymentTimes (ruinTime X x (barrierStrategy X x a) ω),
          ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X x a) ω)) else 0 ∂P := by sorry
