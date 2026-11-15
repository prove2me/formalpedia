-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_kernel_crossing_indicator_set_integral
-- name    : AvramDividend.Classical.avram_bvb_obstruction_uniform_kernel_crossing_indicator_set_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T00:54:48.409327+00:00
-- url     : https://prove2.me/theorems/3fa404e9-f3e8-4f01-908b-fe352fe2f946
-- title:
--   Original uniform negative crossing kernel indicator restricts the mark integral to (-1,-y)
-- statement:
--   For 0<y<1, the compensated affine negative-jump kernel supported on (−1,0) is zero for marks z≥−y, and the integral reduces exactly to the affine function on (−1,−y). No boundary mass is introduced.
-- source:
--   The negative crossing event y+z<0 is z∈Iio(−y); intersecting with the actual Lévy mark support Ioo(−1,0) yields Ioo(−1,−y). Integral of the indicator agrees with integration over the restricted intersection.

import Mathlib
open MeasureTheory Set Real

theorem AvramDividend.Classical.avram_bvb_obstruction_uniform_kernel_crossing_indicator_set_integral (y : ℝ) (hy : 0 < y) (hy1 : y < 1) :
    (∫ z in Ioo (-1 : ℝ) 0,
      (if y + z < 0 then -(y + (1 / 2 : ℝ) + z) else 0)
        ∂(volume : Measure ℝ)) =
    (∫ z in Ioo (-1 : ℝ) (-y),
      -(y + (1 / 2 : ℝ) + z) ∂(volume : Measure ℝ)) := by sorry
