-- Prove2me | solution 1 for metric_ball_subset_axis_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/801109c6-0287-456f-b6ae-4b79ff6264e7

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_coordinate_difference_small_inside_ball

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open MeasureTheory Metric EuclideanSpace
open scoped Pointwise
variable {d : ℕ}
theorem _root_.solution {x : EuclideanSpace ℝ (Fin d)} {r L : ℝ}
    (hx : ∀ i : Fin d, x i ∈ Set.Icc r (L - r)) :
    ball x r ⊆ {y : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, y i ∈ Set.Ico (0 : ℝ) L} := by
  intro y hy i
  have hxi := hx i
  have hsub : |y i - x i| < r := coordinate_difference_small_inside_ball (d := d) hy i
  have hy0 : 0 ≤ y i := by
    have hx0 : 0 ≤ x i - r := sub_nonneg.mpr hxi.1
    have : x i - r < y i := by linarith [(abs_lt.mp hsub).1]
    exact hx0.trans (le_of_lt this)
  have hyL : y i < L := by
    have : y i < x i + r := by linarith [(abs_lt.mp hsub).2]
    exact lt_of_lt_of_le this (by linarith [hxi.2])
  exact ⟨hy0, hyL⟩
