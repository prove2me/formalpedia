-- Prove2me | Theorems.Thm_DoCarmoDG_sphere_not_locally_isometric_to_plane
-- name    : DoCarmoDG.sphere_not_locally_isometric_to_plane
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:16:55.082565+00:00
-- url     : https://prove2.me/theorems/7cd9ac71-4f8a-49b5-ad56-e53a1c3c739f
-- title:
--   No piece of the sphere is isometric to a piece of the plane
-- statement:
--   do Carmo §4-3, Exercise 4 (p. 240): no neighbourhood of a point of a sphere may be isometrically mapped into a plane. In the patch formulation: if $x$ parametrizes a piece of the unit sphere and $y$ a piece of a plane over the same nonempty parameter domain, their first fundamental forms cannot coincide — because the Gaussian curvature would then have to agree, while it equals $1$ on the unit sphere and $0$ on a plane. This is the classical reason why no map of the earth preserves all distances.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 4, Section 4-3 (pp. 235-240)

import Definitions.Def_DoCarmo_surface_patch

namespace DoCarmoDG

theorem sphere_not_locally_isometric_to_plane
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (x y : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x) (hy : IsRegularPatch U y)
    (hsphere : ∀ p ∈ U, ‖x p.1 p.2‖ = 1)
    (q N : EuclideanSpace ℝ (Fin 3)) (hN : N ≠ 0)
    (hplane : ∀ p ∈ U, inner ℝ (y p.1 p.2 - q) N = 0) :
    ¬ (∀ p ∈ U,
        coeffE x p.1 p.2 = coeffE y p.1 p.2 ∧
        coeffF x p.1 p.2 = coeffF y p.1 p.2 ∧
        coeffG x p.1 p.2 = coeffG y p.1 p.2) := by sorry

end DoCarmoDG
