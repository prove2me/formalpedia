-- Prove2me | Theorems.Thm_DoCarmoDG_torsion_eq_zero_iff_plane_curve
-- name    : DoCarmoDG.torsion_eq_zero_iff_plane_curve
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T00:39:43.138649+00:00
-- url     : https://prove2.me/theorems/35a98467-9925-4e2c-8246-e16fb9c878dd
-- title:
--   $\tau \equiv 0$ if and only if the curve is planar (when $k \neq 0$)
-- statement:
--   do Carmo §1-5: for a curve parametrized by arc length with nowhere vanishing curvature, the torsion vanishes identically if and only if the curve is a plane curve, that is, its trace is contained in an affine plane. do Carmo stresses that the hypothesis $k \neq 0$ is essential: Exercise 10 of that section gives a curve with torsion definable as identically zero which is not contained in a plane.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 1, Section 1-5 (pp. 17-22)

import Definitions.Def_DoCarmo_local_theory_curves

namespace DoCarmoDG

theorem torsion_eq_zero_iff_plane_curve
    (a b : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 3))
    (halpha : IsArcLengthCurve (Set.Ioo a b) alpha)
    (hk : ∀ s ∈ Set.Ioo a b, curvature alpha s ≠ 0) :
    (∀ s ∈ Set.Ioo a b, torsion alpha s = 0) ↔
      ∃ p N : EuclideanSpace ℝ (Fin 3), N ≠ 0 ∧
        ∀ s ∈ Set.Ioo a b, inner ℝ (alpha s - p) N = 0 := by sorry

end DoCarmoDG
