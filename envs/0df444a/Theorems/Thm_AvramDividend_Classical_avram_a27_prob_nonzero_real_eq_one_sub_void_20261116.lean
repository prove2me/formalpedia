-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_prob_nonzero_real_eq_one_sub_void_20261116
-- name    : AvramDividend.Classical.avram_a27_prob_nonzero_real_eq_one_sub_void_20261116
-- status  : Disproved
-- author  : @WillR
-- created : 2026-11-16T09:25:36.904158+00:00
-- url     : https://prove2.me/theorems/9f985ad5-3a89-4dad-a9dc-4278137c7f84
-- title:
--   Probability that a measurable random variable is nonzero equals one minus the probability of zero
-- statement:
--   For any measurable random variable Z under a probability measure P and any value z, the original-space probability of Z≠z, as a real number, equals 1 minus the original-space probability of Z=z. Apply measure_compl and the finite-real-cast subtraction for probabilities. This supplies the exact Bernoulli parameter identity for source physical B-marked occupied cells.
-- source:
--   Pinned Mathlib MeasureTheory.measure_compl and ENNReal.toReal_sub_of_le for finite probability measures.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a27_prob_nonzero_real_eq_one_sub_void_20261116
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → E) (hZ : Measurable Z) (z : E) :
    (P {ω : Ω | Z ω ≠ z}).toReal =
      1 - (P {ω : Ω | Z ω = z}).toReal := by sorry
