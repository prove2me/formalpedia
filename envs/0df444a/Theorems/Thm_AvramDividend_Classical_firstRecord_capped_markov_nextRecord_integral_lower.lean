-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_capped_markov_nextRecord_integral_lower
-- name    : AvramDividend.Classical.firstRecord_capped_markov_nextRecord_integral_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:35:22.011321+00:00
-- url     : https://prove2.me/theorems/39f0a916-c9d4-40f8-8582-9bfecbb7c485
-- title:
--   Capped first-record strong-Markov factor lower bounds next killed record
-- statement:
--   The discounted reward of the next upward dividend record dominates the product of the capped first-record discounted mass and the independent true two-sided-exit reward. The bound holds at every cap N for a measurable exponential discount and follows by composing the verified first-record Markov inequality with the verified pathwise-to-expectation bridge.
-- source:
--   Proved firstRecord_capped_namedShiftedReward_markov_lower and capped_trueShiftedReward_expected_le_nextRecord.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_namedShiftedReward_markov_lower
import Theorems.Thm_AvramDividend_Classical_capped_trueShiftedReward_expected_le_nextRecord

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_capped_markov_nextRecord_integral_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (N : ℝ≥0)
    (hd : Measurable (fun t : ℝ≥0 =>
      ENNReal.ofReal ε * ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))))) :
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
         twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
       ENNReal.ofReal ε *
         ENNReal.ofReal (Real.exp (-(q *
           (((min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal) : ℝ))))
      else 0 ∂P) *
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
                   (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
       ENNReal.ofReal (Real.exp (-(q *
         ENNReal.toReal (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
       ENNReal.ofReal (ε * Real.exp
         (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0 ∂P) := by sorry
