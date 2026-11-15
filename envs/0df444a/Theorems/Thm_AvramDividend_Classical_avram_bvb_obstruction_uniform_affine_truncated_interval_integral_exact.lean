-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_affine_truncated_interval_integral_exact
-- name    : AvramDividend.Classical.avram_bvb_obstruction_uniform_affine_truncated_interval_integral_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T00:47:06.690208+00:00
-- url     : https://prove2.me/theorems/c05ffb3f-0a4c-4edf-9fae-05744bf5c8b5
-- title:
--   Exact affine truncated interval integral in the negative uniform-jump generator
-- statement:
--   For any real y, the signed real interval integral of −(y+1/2+z) from −1 to −y is y(y−1)/2. This evaluates the active negative-jump crossing part of the compensated uniform(-1,0) generator kernel.
-- source:
--   Elementary antiderivative of an affine function. This interval integral is a source-preserving child of the negative-uniform Lévy compensated generator identity; it avoids jump and dividend conventions entirely.

import Mathlib
open MeasureTheory intervalIntegral Real

theorem AvramDividend.Classical.avram_bvb_obstruction_uniform_affine_truncated_interval_integral_exact (y : ℝ) :
    (∫ z in (-1 : ℝ)..(-y), -(y + (1 / 2 : ℝ) + z)) =
      y * (y - 1) / 2 := by sorry
