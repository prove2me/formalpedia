-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a127_integer_count_nonvoid_probability_first_second_factorial_moment_bounds_20261114
-- name    : AvramDividend.Classical.avram_a127_integer_count_nonvoid_probability_first_second_factorial_moment_bounds_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:38:16.348824+00:00
-- url     : https://prove2.me/theorems/0aabae54-2e21-4799-9fd1-9f841814b428
-- title:
--   Any integrable natural count: nonzero probability lies between mean minus second factorial moment and mean
-- statement:
--   For any measurable nonnegative integer-valued random variable on a probability space with finite first and second moments, its probability of being nonzero is at most its mean and at least its mean minus its second factorial moment. The result is the integrated pointwise inequalities k−k(k−1) ≤ 1_{k>0} ≤ k and is a reusable pure-probability tool for exact small-time Poisson intensities from moments.
-- source:
--   Pinned Mathlib integral_mono_ae, integral_indicator_one, integral_add/sub, and the elementary integer inequality derived from (k−1)^2≥0. No Lévy process or Poisson distribution assumption.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a127_integer_count_nonvoid_probability_first_second_factorial_moment_bounds_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (hFirst : Integrable (fun ω => (K ω : ℝ)) P)
    (hSecond : Integrable (fun ω => (K ω : ℝ) ^ 2) P) :
    let mean : ℝ := ∫ ω, (K ω : ℝ) ∂P
    let second : ℝ := ∫ ω, (K ω : ℝ) ^ 2 ∂P
    mean - (second - mean) ≤
      1 - (P {ω : Ω | K ω = 0}).toReal ∧
      1 - (P {ω : Ω | K ω = 0}).toReal ≤ mean := by sorry
