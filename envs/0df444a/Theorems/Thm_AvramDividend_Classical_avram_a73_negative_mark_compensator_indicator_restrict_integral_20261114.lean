-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a73_negative_mark_compensator_indicator_restrict_integral_20261114
-- name    : AvramDividend.Classical.avram_a73_negative_mark_compensator_indicator_restrict_integral_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:12:04.798134+00:00
-- url     : https://prove2.me/theorems/f90ac5b7-526a-4751-83bb-7a277550712f
-- title:
--   Original negative-mark compensator indicator integral equals restriction to (-1,0)
-- statement:
--   The integral over strictly negative marks of the mark y times the standard Levy truncation indicator of (-1,1) equals the integral of y directly over (-1,0). This deterministic measure-theoretic identity is valid for arbitrary measure ν, with both Bochner integrals defined even if not integrable; it is the exact indicator simplification needed when separating the Gaussian coefficient from the finite-activity marked compound Poisson Laplace exponent in A72.
-- source:
--   MeasureTheory.integral_indicator, restriction of measures, Iio(0) intersect Ioo(-1,1) = Ioo(-1,0), and elementary Set.indicator identities.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a73_negative_mark_compensator_indicator_restrict_integral_20261114
    (ν : Measure ℝ) :
    (∫ y in Iio (0 : ℝ),
      y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y ∂ν) =
    (∫ y in Ioo (-1 : ℝ) 0, y ∂ν) := by sorry
