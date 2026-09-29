-- Prove2me | Theorems.Thm_DoCarmoDG_signedCurvature_eq_deriv_angle
-- name    : DoCarmoDG.signedCurvature_eq_deriv_angle
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:27:32.45505+00:00
-- url     : https://prove2.me/theorems/f6ca3076-270e-46e9-964e-1431e2ccbc4b
-- title:
--   $k = \theta'$
-- statement:
--   do Carmo §1-7 (p. 38) and §1-5, Exercise 3: the signed curvature of a plane curve parametrized by arc length is the rate of change of the angle its tangent makes with a fixed direction, $k(s) = \theta'(s)$. Equivalently $x'' = -k y'$ and $y'' = k x'$.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 1, Section 1-7 (pp. 31-46)

import Definitions.Def_DoCarmo_plane_curves

namespace DoCarmoDG

theorem signedCurvature_eq_deriv_angle
    (l : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 2)) (theta : ℝ → ℝ)
    (halpha : IsClosedUnitSpeedCurve l alpha)
    (htheta : IsAngleFunction alpha theta) :
    ∀ s, signedCurvature alpha s = deriv theta s := by sorry

end DoCarmoDG
