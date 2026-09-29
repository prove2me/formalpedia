-- Prove2me | Theorems.Thm_DoCarmoDG_four_vertex_lemma
-- name    : DoCarmoDG.four_vertex_lemma
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:28:59.72166+00:00
-- url     : https://prove2.me/theorems/259f92a6-fa2a-4276-bf59-8cf13871198e
-- title:
--   Lemma (5): $\int_0^l (Ax + By + C)\,k'\,ds = 0$
-- statement:
--   do Carmo §1-7, the Lemma preceding the four-vertex theorem, equation (5) (p. 38): for a plane closed curve parametrized by arc length and arbitrary real numbers $A$, $B$, $C$,
--
--   $$ \int_0^l (Ax + By + C)\,\frac{dk}{ds}\,ds = 0 . $$
--
--   The proof integrates by parts and uses $x'' = -ky'$, $y'' = kx'$ together with the fact that all the functions involved agree at $0$ and $l$.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 1, Section 1-7 (pp. 31-46)

import Definitions.Def_DoCarmo_plane_curves

namespace DoCarmoDG

theorem four_vertex_lemma
    (l : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 2))
    (halpha : IsClosedUnitSpeedCurve l alpha) (A B C : ℝ) :
    (∫ s in (0 : ℝ)..l,
        (A * alpha s 0 + B * alpha s 1 + C) * deriv (signedCurvature alpha) s) = 0 := by sorry

end DoCarmoDG
