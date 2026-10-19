-- Prove2me | solution 1 for coordinate_abs_bounded_by_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/3ad49be1-1bf5-4822-9cd6-7208e62869e7

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
theorem _root_.solution (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |x i| ≤ ‖x‖ := by
  simpa [EuclideanSpace.inner_single_left, PiLp.norm_single] using!
    abs_real_inner_le_norm (EuclideanSpace.single i (1 : ℝ)) x
