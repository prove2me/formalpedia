-- Prove2me | Theorems.Thm_Erdos9796Mission_equilateral_bisector_collision
-- name    : Erdos9796Mission.equilateral_bisector_collision
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-12T22:51:58.629658+00:00
-- url     : https://prove2.me/theorems/5f9a8350-6e57-427b-8bfd-cd48a2d1a867
-- title:
--   An equilateral bisector configuration forces a collision
-- statement:
--   Let p be at the same positive distance r from a, b, and c, with a and b also at distance r. If x is at distance r from a and b and its distance from c equals the distance from c to a, then p = x or c = b.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/a0f73bc1ed1e7e57ec5ccc36fe7ca934ce1adaf6/lean/Erdos9796Proof/P97/Census554/FivePointCollision.lean#L93-L168

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Definitions.Def_Erdos9796Mission

open scoped EuclideanGeometry

/-! An equilateral-bisector metric configuration forces one of two collisions. -/

theorem Erdos9796Mission.equilateral_bisector_collision
    {p a b c x : Erdos9796Mission.Plane} {r : ℝ} (hr : 0 < r)
    (hpa : dist p a = r) (hpb : dist p b = r) (hpc : dist p c = r)
    (hab : dist a b = r) (hax : dist a x = r) (hbx : dist b x = r)
    (hcxca : dist c x = dist c a) :
    p = x ∨ c = b := by
  sorry
