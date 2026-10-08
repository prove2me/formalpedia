-- Prove2me | Theorems.Thm_FlowCalculus_unit_half_rotation_image_second_plane_zero
-- name    : FlowCalculus.unit_half_rotation_image_second_plane_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T10:08:51.289981+00:00
-- url     : https://prove2.me/theorems/cf5a4c28-bf13-4788-a161-4f73d4e02c92
-- title:
--   Intertwining unit and half-speed rotations collapses the second plane
-- statement:
--   Let $f:\mathbb R^4\to\mathbb R^4$ be smooth. Let $J$ rotate both coordinate planes at unit angular speed and $K$ rotate the first at unit speed and the second at half speed:
--   $$J(y)=(-y_1,y_0,-y_3,y_2),\qquad K(z)=(-z_1,z_0,-z_3/2,z_2/2).$$
--   If
--   $$Df_y J(y)=K(f(y))\qquad(y\in S^3),$$
--   then $f(y)_2=f(y)_3=0$ for every $y\in S^3$. Thus any smooth map intertwining these rotations sends the sphere into the first coordinate plane; no hypothesis that its image lies on a sphere is needed. This supplies a period obstruction for semiconjugacies of rotations.
-- source:
--   Geiges, Contact geometry, https://arxiv.org/pdf/math/0307242, Remark 2.21(1), printed p. 15. Consequence of the displayed Reeb field at t = 0 and t = 1: source period 2π and target second-plane rotation by π.

import Definitions.Def_GrayStability_HopfFamily
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false
open GrayStability
open scoped ContDiff

theorem FlowCalculus.unit_half_rotation_image_second_plane_zero
    (f : E 4 → E 4) (hf : ContDiff ℝ ∞ f)
    (hR : ∀ y ∈ levelSet unitSphereEquation,
      fderiv ℝ f y ![-y 1, y 0, -y 3, y 2] =
        ![-(f y) 1, (f y) 0, -(f y) 3 / 2, (f y) 2 / 2]) :
    ∀ y ∈ levelSet unitSphereEquation, (f y) 2 = 0 ∧ (f y) 3 = 0 := by sorry
