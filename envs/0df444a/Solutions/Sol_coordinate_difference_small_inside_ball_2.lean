-- Prove2me | solution 2 for coordinate_difference_small_inside_ball
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:20:07.965737+00:00
-- url     : https://prove2.me/submissions/1773f2cc-7c29-40bf-b640-3e4a9aa7f2e3

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open MeasureTheory Metric EuclideanSpace
open scoped Pointwise
variable {d : ℕ}


theorem solution {x y : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hy : y ∈ ball x r)
    (i : Fin d) : |y i - x i| < r := by
  have h1 : ‖(y - x) i‖ ≤ ‖y - x‖ := PiLp.norm_apply_le (y - x) i
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have h2 : (y - x) i = y i - x i := rfl
  rw [h2, Real.norm_eq_abs] at h1
  linarith

