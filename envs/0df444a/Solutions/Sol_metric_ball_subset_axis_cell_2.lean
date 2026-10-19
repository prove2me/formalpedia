-- Prove2me | solution 2 for metric_ball_subset_axis_cell
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:04:23.907758+00:00
-- url     : https://prove2.me/submissions/bf183c2c-a001-4576-ad23-fef8d716ff01

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


theorem solution {x : EuclideanSpace ℝ (Fin d)} {r L : ℝ}
    (hx : ∀ i : Fin d, x i ∈ Set.Icc r (L - r)) :
    ball x r ⊆ {y : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, y i ∈ Set.Ico (0 : ℝ) L} := by
  intro y hy
  simp only [Set.mem_setOf_eq, Set.mem_Ico]
  intro i
  have hd : dist y x < r := hy
  have hi : |y i - x i| < r := by
    have h := EuclideanSpace.dist_eq y x
    have : |y i - x i| ≤ dist y x := by
      rw [← Real.dist_eq]
      exact PiLp.dist_apply_le y x i
    linarith
  rw [abs_lt] at hi
  have := hx i
  simp only [Set.mem_Icc] at this
  constructor <;> linarith

