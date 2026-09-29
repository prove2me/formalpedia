-- Prove2me | Theorems.Thm_Erdos9796Mission_three_triad_collision
-- name    : Erdos9796Mission.three_triad_collision
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-12T22:52:18.344658+00:00
-- url     : https://prove2.me/theorems/5143e3ab-5889-4628-bc00-618465ab3161
-- title:
--   Three linked equal-distance triads force a collision
-- statement:
--   For five planar points A, B, C, D, and E, suppose B has equal distances to C and D, that common distance equals the distance from D to A, C has equal distances to A, D, and E, and E has equal distances to A, B, and D. Then A = B.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/a0f73bc1ed1e7e57ec5ccc36fe7ca934ce1adaf6/lean/Erdos9796Proof/P97/Census554/ThreeTriadCollision.lean#L143-L207

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796Mission

open scoped EuclideanGeometry

/-!
# Three linked equal-distance triads force a collision

Five points in the Euclidean plane with the displayed chain of equal-distance
relations must have `A = B`.
-/

theorem Erdos9796Mission.three_triad_collision
    {A B C D E : Erdos9796Mission.Plane}
    (hBC_BD : dist B C = dist B D)
    (hBD_DA : dist B D = dist D A)
    (hCA_CD : dist C A = dist C D)
    (hCD_CE : dist C D = dist C E)
    (hEA_EB : dist E A = dist E B)
    (hEB_ED : dist E B = dist E D) : A = B := by sorry
