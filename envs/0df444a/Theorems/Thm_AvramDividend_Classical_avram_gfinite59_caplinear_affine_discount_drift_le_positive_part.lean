-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite59_caplinear_affine_discount_drift_le_positive_part
-- name    : AvramDividend.Classical.avram_gfinite59_caplinear_affine_discount_drift_le_positive_part
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T23:17:42.424782+00:00
-- url     : https://prove2.me/theorems/dca71000-5cfd-4ac1-b67f-a6619d59ba5e
-- title:
--   Upper cap-linear discounted affine drift bounded by nonnegative drift
-- statement:
--   For a nonnegative value at the cap-linear cutoff, nonnegative discount and a point above cutoff, the affine continuation contributes discounted drift at most the positive part of the original process drift. Direct deterministic scalar component of the original Gaussian upper-strip generator estimate; replaces a failed publisher specification with ambiguous process binders.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_gfinite59_caplinear_affine_discount_drift_le_positive_part
    (c q wb b y : ℝ) (hq : 0 ≤ q)
    (hwb : 0 ≤ wb) (hby : b ≤ y) :
    c - q * (wb + (y - b)) ≤ max c 0 := by
  sorry
