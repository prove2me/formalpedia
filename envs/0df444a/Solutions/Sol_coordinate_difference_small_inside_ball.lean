-- Prove2me | solution 1 for coordinate_difference_small_inside_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/13a04d43-d930-43c9-be81-d95ca899e223

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_coordinate_abs_bounded_by_norm

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open MeasureTheory Metric EuclideanSpace
open scoped Pointwise
variable {d : ℕ}
theorem _root_.solution {x y : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hy : y ∈ ball x r)
    (i : Fin d) : |y i - x i| < r := by
  have hnorm : ‖y - x‖ < r := by simpa [Metric.mem_ball, dist_eq_norm, dist_comm] using! hy
  exact lt_of_le_of_lt (by simpa using! coordinate_abs_bounded_by_norm (d := d) (y - x) i) hnorm
