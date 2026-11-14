-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a198_positive_weighted_Gaussian_abs_tail_le_chernoff_plus_square
-- name    : AvramDividend.Classical.avram_ga_a198_positive_weighted_Gaussian_abs_tail_le_chernoff_plus_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:21:39.567312+00:00
-- url     : https://prove2.me/theorems/f6197441-4adf-46f3-a482-50c773aaf70d
-- title:
--   Positive Esscher tilt plus centred square energy dominates two-sided weighted Gaussian large-absolute-increment tail
-- statement:
--   When the exponential source weight θ is nonnegative, its contribution on the positive large Gaussian-increment tail is bounded by an Esscher transform with an arbitrary nonnegative positive tilt r. On the negative large-increment tail the exponential is at most one and is bounded by z squared over the positive threshold squared. Thus the weighted two-sided large tail is dominated pointwise by a positive-tilt exponential plus ordinary truncated centred square energy, using only the existing Proved positive Gaussian MGF and raw square tail results. This is a stronger source-adapted alternative to helper a196, aimed at closing the large Taylor component of original a149.
-- source:
--   Positive Gaussian exponential Chernoff comparison and squared negative-tail energy.

import Mathlib
open Real
noncomputable section

theorem AvramDividend.Classical.avram_ga_a198_positive_weighted_Gaussian_abs_tail_le_chernoff_plus_square
    (θ r δ z : ℝ) (hθ : 0 ≤ θ) (hr : 0 ≤ r) (hδ : 0 < δ) :
    (if δ ≤ |z| then Real.exp (θ * z) else 0) ≤
      Real.exp (-r * δ) * Real.exp ((θ + r) * z) +
        (if δ ≤ |z| then z^2 / δ^2 else 0) := by sorry
