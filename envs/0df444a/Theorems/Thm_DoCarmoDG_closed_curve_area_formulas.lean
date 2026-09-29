-- Prove2me | Theorems.Thm_DoCarmoDG_closed_curve_area_formulas
-- name    : DoCarmoDG.closed_curve_area_formulas
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:26:28.169601+00:00
-- url     : https://prove2.me/theorems/31878b3b-1773-4d03-97de-14d5779671f2
-- title:
--   The three forms of the area formula (1)
-- statement:
--   do Carmo §1-7, equation (1) (p. 33). For a closed curve the three expressions
--
--   $$ \int_0^l x y'\,dt, \qquad -\int_0^l y x'\,dt, \qquad \frac12\int_0^l (x y' - y x')\,dt $$
--
--   coincide; do Carmo derives the second from the first by integrating $(xy)'$ over a period, and the third is then immediate.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 1, Section 1-7 (pp. 31-46)

import Definitions.Def_DoCarmo_plane_curves

namespace DoCarmoDG

theorem closed_curve_area_formulas
    (l : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 2))
    (halpha : IsClosedUnitSpeedCurve l alpha) :
    (∫ t in (0 : ℝ)..l, alpha t 0 * deriv alpha t 1) =
        -∫ t in (0 : ℝ)..l, alpha t 1 * deriv alpha t 0 ∧
      signedArea l alpha = ∫ t in (0 : ℝ)..l, alpha t 0 * deriv alpha t 1 := by sorry

end DoCarmoDG
