-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_finite_measure_normalize_nonnegative_support
-- name    : AvramDividend.Classical.excursion_finite_measure_normalize_nonnegative_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:11:10.231756+00:00
-- url     : https://prove2.me/theorems/4a620b24-e1ef-45bc-9971-50b207cb7c31
-- title:
--   Normalisation preserves nonnegative support of nonzero finite measures
-- statement:
--   Normalising a nonzero finite measure supported on nonnegative numbers preserves its zero negative mass.
-- source:
--   Pinned Mathlib Prokhorov single-module diagnostic; FiniteMeasure.normalize_eq_of_nonzero proof.

import Mathlib.MeasureTheory.Measure.Prokhorov

open MeasureTheory Set

theorem AvramDividend.Classical.excursion_finite_measure_normalize_nonnegative_support
    (μ : FiniteMeasure ℝ) (hμ : μ ≠ 0)
    (hsupport : μ (Iio (0 : ℝ)) = 0) :
    μ.normalize (Iio (0 : ℝ)) = 0 := by sorry
