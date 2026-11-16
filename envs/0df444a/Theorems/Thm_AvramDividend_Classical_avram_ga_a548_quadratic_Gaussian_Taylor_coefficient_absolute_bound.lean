-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a548_quadratic_Gaussian_Taylor_coefficient_absolute_bound
-- name    : AvramDividend.Classical.avram_ga_a548_quadratic_Gaussian_Taylor_coefficient_absolute_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:55:01.164235+00:00
-- url     : https://prove2.me/theorems/ac9e007b-a518-4992-bf91-3a84007e73c9
-- title:
--   Quadratic Gaussian Taylor polynomial controlled by bounded first and second coefficients
-- statement:
--   If first and second Taylor coefficients have absolute values at most B, the absolute quadratic Taylor correction is bounded by B(2+s)(1+z squared) for nonnegative variance scale s.
-- source:
--   Real triangle inequality, |z²-s|≤z²+s, |z|≤1+z² and elementary algebra.

import Mathlib
open MeasureTheory Set Filter
noncomputable section

theorem AvramDividend.Classical.avram_ga_a548_quadratic_Gaussian_Taylor_coefficient_absolute_bound
    (B u v z s : ℝ) (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hu : |u| ≤ B) (hv : |v| ≤ B) :
    |u*z + v/2*(z^2-s)| ≤ B*(2+s)*(1+z^2) := by sorry
