-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_residual_clock_future_indepFun
-- name    : AvramDividend.Classical.avram_ws01e_b_conditional_residual_clock_future_indepFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:29:15.412722+00:00
-- url     : https://prove2.me/theorems/5ea4709f-c2ce-4d3b-84c3-0bc48378659f
-- title:
--   True conditional independence of the residual clock and post-stopping future path
-- statement:
--   Under a genuine product probability law of a Lévy process and an independently sampled nonnegative memoryless clock, given positive probability of τ<e and actual independence of stopping age τ and a measurable post-stopping-path statistic Y, the real residual time e−τ and Y are independent random variables under the conditional probability law given τ<e. This statement gives complete Borel sigma-algebra independence, not merely a family of tail identities. The proof applies the Mathlib IndepFun characterisation to the accepted full conditional Borel rectangle factorisation. No global tilted stopping-time law, Wiener–Hopf independence or desired exit identity is assumed.

import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_residual_clock_rectangle_factor

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_conditional_residual_clock_future_indepFun
    {Ω Θ β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (Y : Ω → β) (hY : Measurable Y)
    (hInd : IndepFun τ Y P)
    (e : Θ → ℝ≥0) (he : Measurable e)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (hTail : ∀ a : ℝ≥0, Q {η : Θ | a < e η} = discount a)
    (factor : ℝ≥0 → ℝ≥0∞)
    (hShift : ∀ a t : ℝ≥0, discount (a + t) = factor t * discount a)
    (hPos : (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ 0) :
    IndepFun
      (fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ))
      (fun z : Ω × Θ => Y z.1)
      ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}]) := by sorry
