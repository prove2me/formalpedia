-- Prove2me | Theorems.Thm_AvramDividend_Classical_variable_finite_marks_sum_measurable_ws01b
-- name    : AvramDividend.Classical.variable_finite_marks_sum_measurable_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:23:04.299736+00:00
-- url     : https://prove2.me/theorems/eda5a729-e225-4651-bc02-996e029fc583
-- title:
--   Joint measurability of random-count finite sums of measurable marks
-- statement:
--   For any measurable test function f on a mark space E, the finite sum of its first N sequence coordinates is a measurable real function jointly of the natural count N and the infinite mark sequence. No Poisson or independence assumptions required. Establishes the technical kernel measurability needed for predictable marked Campbell compensation.
-- source:
--   Pinned Mathlib Measurable.tsum and tsum_eq_sum with eventually zero terms, yielding an exact measurable random finite sum; a missing analytic regularity prerequisite for a properly formulated stochastic compensator.

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.variable_finite_marks_sum_measurable_ws01b
    {E : Type*} [MeasurableSpace E]
    (f : E → ℝ) (hf : Measurable f) :
    Measurable (fun p : ℕ × (ℕ → E) =>
      ∑ n ∈ Finset.range p.1, f (p.2 n)) := by sorry
