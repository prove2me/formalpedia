-- Prove2me | Theorems.Thm_DoCarmoDG_angle_function_exists
-- name    : DoCarmoDG.angle_function_exists
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:27:02.0169+00:00
-- url     : https://prove2.me/theorems/b54f9f19-c237-4b8d-8a90-c69af060e649
-- title:
--   Existence of a smooth angle function
-- statement:
--   do Carmo §1-7 (p. 38, and §1-5, Exercise 3): for a plane curve parametrized by arc length there exists a differentiable function $\theta$ with $x'(s) = \cos\theta(s)$, $y'(s) = \sin\theta(s)$ — a smooth lift of the tangent indicatrix to the real line. do Carmo uses this function to define the rotation index and in the proof of the lemma preceding the four-vertex theorem.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 1, Section 1-7 (pp. 31-46)

import Definitions.Def_DoCarmo_plane_curves

namespace DoCarmoDG

theorem angle_function_exists
    (l : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 2))
    (halpha : IsClosedUnitSpeedCurve l alpha) :
    ∃ theta : ℝ → ℝ, IsAngleFunction alpha theta := by sorry

end DoCarmoDG
