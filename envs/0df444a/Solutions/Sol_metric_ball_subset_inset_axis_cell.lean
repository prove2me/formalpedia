-- Prove2me | solution 1 for metric_ball_subset_inset_axis_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/9e76db8c-b1f7-458e-818a-1b90e4459450

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_metric_ball_subset_axis_cell

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise
variable {d : ℕ}
theorem _root_.solution {L r : ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ insetAxisAlignedCell (d := d) L r) :
    ball x r ⊆ axisAlignedCell (d := d) L := by
  simpa [axisAlignedCell, insetAxisAlignedCell] using!
    metric_ball_subset_axis_cell (d := d) (x := x) (r := r) (L := L) hx
