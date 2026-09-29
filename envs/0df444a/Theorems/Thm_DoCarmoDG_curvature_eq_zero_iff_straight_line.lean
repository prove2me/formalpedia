-- Prove2me | Theorems.Thm_DoCarmoDG_curvature_eq_zero_iff_straight_line
-- name    : DoCarmoDG.curvature_eq_zero_iff_straight_line
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T00:38:53.336678+00:00
-- url     : https://prove2.me/theorems/34fa78aa-b5ed-41da-a918-4563cd1c98d7
-- title:
--   $k \equiv 0$ if and only if the curve is a straight line
-- statement:
--   do Carmo §1-5, immediately after the definition of curvature: a curve parametrized by arc length is a straight line, $\alpha(s) = su + v$ with $|u| = 1$, if and only if its curvature vanishes identically. One direction is the computation $k \equiv 0$ for a line; the converse follows by integrating $\alpha'' \equiv 0$ twice.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 1, Section 1-5 (pp. 17-22)

import Definitions.Def_DoCarmo_local_theory_curves

namespace DoCarmoDG

theorem curvature_eq_zero_iff_straight_line
    (a b : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 3))
    (halpha : IsArcLengthCurve (Set.Ioo a b) alpha) :
    (∀ s ∈ Set.Ioo a b, curvature alpha s = 0) ↔
      ∃ u v : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 ∧ ∀ s ∈ Set.Ioo a b, alpha s = s • u + v := by
  sorry

end DoCarmoDG
