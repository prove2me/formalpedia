-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_rescaled_probability_support_mass
-- name    : AvramDividend.Classical.excursion_rescaled_probability_support_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:21:17.911864+00:00
-- url     : https://prove2.me/theorems/7880b553-f622-460a-9d25-7fde6b88700b
-- title:
--   Rescaled probability weak limit retains nonnegative support and exact mass
-- statement:
--   Multiplying a probability measure supported on nonnegative reals by a nonnegative finite scalar c preserves its vanishing mass below zero and yields total mass c. The result is used to construct the unnormalised weak limit of tight Lévy excursion resolvents.
-- source:
--   Mathlib FiniteMeasure.toMeasure_smul; probability mass one and null-set scalar multiplication.

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasure

open MeasureTheory Set

theorem AvramDividend.Classical.excursion_rescaled_probability_support_mass
    (P : ProbabilityMeasure ℝ) (c : NNReal)
    (hP : (P : Measure ℝ) (Iio (0 : ℝ)) = 0) :
    ((c • P.toFiniteMeasure : FiniteMeasure ℝ) : Measure ℝ) (Iio (0 : ℝ)) = 0 ∧
    ((c • P.toFiniteMeasure : FiniteMeasure ℝ) : Measure ℝ) Set.univ =
      (c : ENNReal) := by sorry
