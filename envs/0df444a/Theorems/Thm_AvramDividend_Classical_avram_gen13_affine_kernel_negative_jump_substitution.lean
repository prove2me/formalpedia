-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen13_affine_kernel_negative_jump_substitution
-- name    : AvramDividend.Classical.avram_gen13_affine_kernel_negative_jump_substitution
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:22:47.012205+00:00
-- url     : https://prove2.me/theorems/b0fd29a7-16dc-406d-827e-592ef620e7c1
-- title:
--   Convert the affine ruin-crossing negative-jump kernel to positive magnitude coordinates
-- statement:
--   Change the sign of the negative jump mark in the crossing-ruin affine generator integral. The resulting positive-magnitude kernel is the difference of the half-power and three-halves-power terms. This preserves the exact source integrand on a truncated negative-jump interval.
-- source:
--   Pinned intervalIntegral.integral_comp_neg, integral_congr and Real.rpow_add; analytic bridge before the original Levy measure transformation.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_gen13_affine_kernel_negative_jump_substitution
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    (∫ z in (-1 : ℝ)..(-y), (-1 - y - z) *
      |z| ^ (-(3 / 2 : ℝ))) =
    (∫ r in y..1, (r ^ (-(1 / 2 : ℝ)) -
      (1 + y) * r ^ (-(3 / 2 : ℝ)))) := by sorry
