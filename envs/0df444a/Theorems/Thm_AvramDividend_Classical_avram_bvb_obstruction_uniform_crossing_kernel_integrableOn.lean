-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_crossing_kernel_integrableOn
-- name    : AvramDividend.Classical.avram_bvb_obstruction_uniform_crossing_kernel_integrableOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:25:22.813608+00:00
-- url     : https://prove2.me/theorems/494f99c6-71cf-4739-ad1c-16d9ef716de6
-- title:
--   Negative-unit compensated affine crossing-jump kernel is integrable over its exact Lévy mark interval
-- statement:
--   For any reserve y, the crossing-jump kernel −(y+1/2+z) on negative marks z<−y and zero otherwise is Lebesgue integrable on the original uniform negative-unit mark interval (−1,0). This is the missing true GeneratorIntegrable hypothesis for the positive-cap original Lévy HJB example.
-- source:
--   The piecewise kernel is the indicator of Iio(-y) times a globally continuous affine function. The affine function is integrable on compact [-1,0], hence on the intersection with (-1,0). Pinned integrableOn_indicator_iff gives the result.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.avram_bvb_obstruction_uniform_crossing_kernel_integrableOn (y : ℝ) :
    IntegrableOn (fun z : ℝ =>
      if y + z < 0 then -(y + (1 / 2 : ℝ) + z) else 0)
      (Ioo (-1 : ℝ) 0) (volume : Measure ℝ) := by sorry
