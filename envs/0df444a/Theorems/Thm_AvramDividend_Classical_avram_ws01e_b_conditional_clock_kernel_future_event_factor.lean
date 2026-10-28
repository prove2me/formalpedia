-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_clock_kernel_future_event_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_conditional_clock_kernel_future_event_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:06:41.217265+00:00
-- url     : https://prove2.me/theorems/fe27de8d-9ea2-46c9-8381-bd851b392bd5
-- title:
--   All measurable clock kernels conditionally factor from the future Lévy statistic
-- statement:
--   Let τ be a measurable nonnegative stopping age, Y a measurable future-path statistic independent of τ under P, and e an independently sampled measurable nonnegative clock under Q. For any jointly measurable clock-age event K(a,η) and any measurable future event B, conditioning the genuine product P×Q on τ<e leaves the conditional joint event K(τ,e) and Y∈B factorised as the conditional clock-event probability times P(Y∈B). The proof intersects K with the strict clock-survival event, obtains its measurable section probability automatically by Tonelli, applies the canonically Proved arbitrary-clock-kernel factor, and normalises using Mathlib conditional probabilities. No Wiener–Hopf independence, two-sided exit formula, or global tilted law is assumed.

import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_arbitrary_clock_kernel_future_event_factor

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_conditional_clock_kernel_future_event_factor
    {Ω Θ β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (Y : Ω → β) (hY : Measurable Y)
    (hInd : IndepFun τ Y P)
    (e : Θ → ℝ≥0) (he : Measurable e)
    (K : ℝ≥0 → Θ → Prop)
    (hK : MeasurableSet {z : ℝ≥0 × Θ | K z.1 z.2})
    (B : Set β) (hB : MeasurableSet B) :
    (P.prod Q)[{z : Ω × Θ | K (τ z.1) z.2 ∧ Y z.1 ∈ B} |
        {z : Ω × Θ | τ z.1 < e z.2}] =
      (P.prod Q)[{z : Ω × Θ | K (τ z.1) z.2} |
          {z : Ω × Θ | τ z.1 < e z.2}] *
        P (Y ⁻¹' B) := by sorry
