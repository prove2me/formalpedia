-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_independent_clock_positive_survival_event
-- name    : AvramDividend.Classical.avram_ws01e_b_independent_clock_positive_survival_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:57:44.087711+00:00
-- url     : https://prove2.me/theorems/7497827a-f38d-4b24-9290-75bb6512faa0
-- title:
--   A positive-survival independent clock outlives any finite measurable stopping age with positive probability
-- statement:
--   For any probability P on a Lévy sample space and independent clock probability Q, any measurable finite nonnegative stopping age τ and measurable nonnegative clock e satisfying strictly positive tail probability Q(e>a)>0 at every finite age a, the genuine joint product probability P×Q(τ<e) is nonzero. The proof uses Tonelli's product-section integration and the fact that a measurable nonnegative integrand strictly positive at every sample cannot have zero integral under a probability. This supplies the missing positive conditioning-event hypothesis for finite stopped-clock regeneration results, without assuming exponential memorylessness or Wiener–Hopf independence.
-- source:
--   Pinned Mathlib Measure.prod_apply, measurable_measure_prodMk_left, lintegral_eq_zero_iff and positive probability nonempty AE filter; a standard Tonelli argument.

import Mathlib

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_independent_clock_positive_survival_event
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (e : Θ → ℝ≥0) (he : Measurable e)
    (hTailPos : ∀ a : ℝ≥0, 0 < Q {η : Θ | a < e η}) :
    (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ 0 := by sorry
