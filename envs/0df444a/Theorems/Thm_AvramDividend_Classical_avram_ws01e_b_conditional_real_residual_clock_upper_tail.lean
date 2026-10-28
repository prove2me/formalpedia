-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_real_residual_clock_upper_tail
-- name    : AvramDividend.Classical.avram_ws01e_b_conditional_real_residual_clock_upper_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:52:00.620988+00:00
-- url     : https://prove2.me/theorems/e6ea2c33-e3fd-427a-b7a8-c7ce7aef5fe6
-- title:
--   Real residual observation clock has the exact memoryless conditional upper-ray law
-- statement:
--   For a measurable nonnegative stopping age τ and an independently sampled nonnegative clock e with strictly memoryless survival kernel factor(t), under actual product law P×Q conditioned on the positive-probability event τ<e, the genuine real residual variable e−τ has tail probability P(e−τ>t | τ<e)=factor(t) for all nonnegative t. This is an exact random-variable distributional statement; the accepted conditional residual age-shift identity uses the event τ+t<e. The proof identifies those events via the real embedding of nonnegative times and uses the accepted residual-clock conditional tail with an all-path event. It supplies the positive upper rays needed for a separate uniqueness proof that the residual clock has the fresh exponential distribution.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_residual_clock_future_tail

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_conditional_real_residual_clock_upper_tail
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
    (t : ℝ≥0) :
    (P.prod Q)[{z : Ω × Θ |
      (t : ℝ) < (e z.2 : ℝ) - (τ z.1 : ℝ)} |
      {z : Ω × Θ | τ z.1 < e z.2}] = factor t := by sorry
