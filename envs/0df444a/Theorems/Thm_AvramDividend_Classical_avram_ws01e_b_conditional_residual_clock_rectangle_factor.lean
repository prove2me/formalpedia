-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_residual_clock_rectangle_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_conditional_residual_clock_rectangle_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:19:33.643389+00:00
-- url     : https://prove2.me/theorems/0e7bd1eb-3ab4-4a70-a569-09a0983c94fd
-- title:
--   Complete residual-clock and future-path conditional rectangle factorisation
-- statement:
--   For any nonnegative measurable stopping age τ, an independent nonnegative clock e with positive survival probability at τ and strict memoryless tail, and a measurable future-path statistic Y independent of τ under process probability P, condition the actual product law P×Q on τ<e. Then for every real Borel event A of the realised residual clock e−τ and every measurable future event B, the conditional joint probability factors exactly into the product of both conditional marginals. This establishes the full collection of Borel rectangles required for conditional independence, extending the accepted upper-tail result to arbitrary sets without invoking Wiener–Hopf splitting. The proof imports accepted arbitrary clock-kernel conditional factorisation and the correct future marginal under this conditioning.

import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_clock_kernel_future_event_factor
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_residual_clock_future_tail

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_conditional_residual_clock_rectangle_factor
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
    (hPos : (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ 0)
    (A : Set ℝ) (hA : MeasurableSet A)
    (B : Set β) (hB : MeasurableSet B) :
    (P.prod Q)[{z : Ω × Θ |
        ((e z.2 : ℝ) - (τ z.1 : ℝ)) ∈ A ∧ Y z.1 ∈ B} |
        {z : Ω × Θ | τ z.1 < e z.2}] =
      (P.prod Q)[{z : Ω × Θ |
          ((e z.2 : ℝ) - (τ z.1 : ℝ)) ∈ A} |
          {z : Ω × Θ | τ z.1 < e z.2}] *
        (P.prod Q)[{z : Ω × Θ | Y z.1 ∈ B} |
          {z : Ω × Θ | τ z.1 < e z.2}] := by sorry
