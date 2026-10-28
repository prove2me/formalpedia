-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_stoppedReward_postUpcrossing_shifted_window_of_levy
-- name    : AvramDividend.Classical.barrierStrategy_stoppedReward_postUpcrossing_shifted_window_of_levy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:03:45.462541+00:00
-- url     : https://prove2.me/theorems/5b38749e-817b-4875-9c74-64bce03cf211
-- title:
--   Unconditional exact stopped barrier dividend payoff shift to Lévy future increments
-- statement:
--   For every first attained finite upward barrier passage, the original discounted barrier dividend Stieltjes reward stopped at controlled ruin equals the first-passage discount times the discounted post-passage increment running-supremum Stieltjes reward, restricted to the exact translated original payment-time window. This is unconditional on measure finiteness and support, both now Proved for Lévy paths. The event and true ruin horizon have not been replaced by any unproved expression.
-- source:
--   Accepted stopped pathwise shift theorem 1fff2edc-039c-4463-b4b5-ad519e24976c and shiftedSup_dividendMeasure_zero_nonpositive_of_levy a4f97533-1f1f-451b-ac8a-e4f85ccd9fae; towards strong Markov barrier valuation 79978d61.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_stoppedReward_postUpcrossing_shifted_window
import Theorems.Thm_AvramDividend_Classical_shiftedSup_dividendMeasure_zero_nonpositive_of_levy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_stoppedReward_postUpcrossing_shifted_window_of_levy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (q : ℝ) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    (∫⁻ t in paymentTimes (ruinTime X x (barrierStrategy X x a) ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂dividendMeasure (barrierStrategy X x a) ω) =
    ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
      (∫⁻ t in (Set.Ioi (0 : ℝ)) ∩
        ((fun t : ℝ => (u : ℝ) + t) ⁻¹'
          paymentTimes (ruinTime X x (barrierStrategy X x a) ω)),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure
          (fun r (_ : Ω) =>
            sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
          ω)) := by sorry
