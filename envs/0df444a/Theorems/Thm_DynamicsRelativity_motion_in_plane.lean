-- Prove2me | Theorems.Thm_DynamicsRelativity_motion_in_plane
-- name    : DynamicsRelativity.motion_in_plane
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T23:17:57.199448+00:00
-- url     : https://prove2.me/theorems/047696bd-55b4-4d21-9925-e33eddb0d900
-- title:
--   Motion in a central force field takes place in a plane
-- statement:
--   Let a particle of mass $m>0$ move in an arbitrary central force field with radial profile $F$. Because the angular momentum $L$ is a fixed vector satisfying $L\cdot x=0$ by construction, the position of the particle always lies in the plane through the origin perpendicular to $L$; by the same argument $L\cdot\dot x=0$, so the velocity lies in that plane too. Formally, for every time $t$,
--
--   $$ \big\langle L(0),\,x(t)\big\rangle = 0 \qquad\text{and}\qquad \big\langle L(0),\,\dot x(t)\big\rangle = 0 , $$
--
--   where $L(0)=m\,x(0)\times\dot x(0)$.
--
--   This is what reduces the three-dimensional problem to a problem in a plane, and it is the step that licenses the plane polar coordinates used for the rest of the chapter.
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, http://www.damtp.cam.ac.uk/user/tong/relativity.html — §4, p. 48 ("all motion takes place in a plane … $L\cdot x = 0$ … By the same argument, $L\cdot\dot x = 0$").

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.motion_in_plane {m : ℝ} {F : ℝ → ℝ} {x : ℝ → Vec}
    (h : CentralForceMotion m F x) (t : ℝ) :
    inner ℝ (angularMomentum m x 0) (x t) = 0 ∧
      inner ℝ (angularMomentum m x 0) (vel x t) = 0 := by sorry
