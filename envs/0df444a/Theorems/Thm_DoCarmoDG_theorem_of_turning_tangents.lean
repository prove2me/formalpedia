-- Prove2me | Theorems.Thm_DoCarmoDG_theorem_of_turning_tangents
-- name    : DoCarmoDG.theorem_of_turning_tangents
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T01:27:53.485112+00:00
-- url     : https://prove2.me/theorems/3992b575-8788-4bc3-8eda-62d60c3cb1e7
-- title:
--   Theorem of turning tangents: the rotation index of a simple closed curve is $\pm 1$
-- statement:
--   **Theorem of turning tangents** (do Carmo §1-7, p. 37): the rotation index of a simple closed curve is $\pm 1$, the sign depending on the orientation of the curve. In terms of an angle function $\theta$, the total turning over one period is
--
--   $$ \theta(l) - \theta(0) = \pm 2\pi . $$
--
--   For a closed but non-simple curve the total turning is $2\pi n$ for some integer $n$, the rotation index; simplicity forces $n = \pm 1$.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 1, Section 1-7 (pp. 31-46)

import Definitions.Def_DoCarmo_plane_curves

namespace DoCarmoDG

theorem theorem_of_turning_tangents
    (l : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 2)) (theta : ℝ → ℝ)
    (halpha : IsSimpleClosedCurve l alpha)
    (htheta : IsAngleFunction alpha theta) :
    theta l - theta 0 = 2 * Real.pi ∨ theta l - theta 0 = -(2 * Real.pi) := by sorry

end DoCarmoDG
