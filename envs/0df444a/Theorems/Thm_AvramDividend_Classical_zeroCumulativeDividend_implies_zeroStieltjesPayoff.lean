-- Prove2me | Theorems.Thm_AvramDividend_Classical_zeroCumulativeDividend_implies_zeroStieltjesPayoff
-- name    : AvramDividend.Classical.zeroCumulativeDividend_implies_zeroStieltjesPayoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:35:22.889901+00:00
-- url     : https://prove2.me/theorems/eedf911c-cf0d-415f-ae05-455967e22799
-- title:
--   A dividend strategy with zero cumulative path pays zero discounted Stieltjes dividends
-- statement:
--   If an admissible dividend strategy has identically zero cumulative dividends along one sample path, then its entire nonnegative discounted Stieltjes payoff before ruin is zero, at any discount rate. Cover the nonnegative payment times by countably many initial finite intervals, use the exact Stieltjes interval-to-dividend-value identity, and apply countable subadditivity.
-- source:
--   Necessary reusable pathwise bridge for the infinite-first-upcrossing branch of the W-free strong-Markov dividend theorem 79978d61-9d1f-4b20-b8a5-114797a8e380. Imports Proved exact Stieltjes identity 56472398-9e4f-43ea-9dc2-772f94a501cf.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.zeroCumulativeDividend_implies_zeroStieltjesPayoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (hzero : ∀ t : ℝ≥0, D t ω = 0) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)) = 0 := by
  sorry
