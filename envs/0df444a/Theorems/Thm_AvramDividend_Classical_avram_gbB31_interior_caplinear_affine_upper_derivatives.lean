-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB31_interior_caplinear_affine_upper_derivatives
-- name    : AvramDividend.Classical.avram_gbB31_interior_caplinear_affine_upper_derivatives
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:18:45.103613+00:00
-- url     : https://prove2.me/theorems/90e5b7db-2205-4f2a-b63c-31816eedfb46
-- title:
--   Interior cap-linear extension has unit derivative and zero curvature above clipping level
-- statement:
--   Above the interior clipping threshold b, a cap-linear extension of any real value function is locally affine with slope one. Consequently its ordinary derivative equals one and second iterated derivative vanishes at every y>b, without requiring any differentiability of the original value function at the cap.
-- source:
--   Eventually equal locally above b to the affine expression w(b)+y-b. Use neighbourhood derivative agreement twice; exact Mathlib revision is pinned.

import Mathlib
open Filter Set
noncomputable section

theorem AvramDividend.Classical.avram_gbB31_interior_caplinear_affine_upper_derivatives
    (w : ℝ → ℝ) (b y : ℝ) (hy : b < y) :
    let V : ℝ → ℝ := fun z =>
      if z ≤ b then w z else w b + (z - b)
    deriv V y = 1 ∧ iteratedDeriv 2 V y = 0 := by sorry
