-- Prove2me | Theorems.Thm_DoCarmoDG_gauss_curvature_reparametrization_invariant
-- name    : DoCarmoDG.gauss_curvature_reparametrization_invariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:16:33.00637+00:00
-- url     : https://prove2.me/theorems/878e3afd-e08d-45da-960f-0de004df0388
-- title:
--   $K$ does not depend on the parametrization
-- statement:
--   Change of parameters (do Carmo §2-3, and §3-3 where $K$ is introduced as a quantity attached to a point of the surface). If two regular patches parametrize the same piece of surface, related by a diffeomorphism $\psi$ of their parameter domains with $x = y \circ \psi$, then their Gaussian curvatures agree at corresponding points, $K_x(p) = K_y(\psi(p))$. Note that $K$ is unchanged even when the change of parameters reverses orientation, since $e$, $f$, $g$ change sign together with $N$.
--
--   This is what allows the Theorema Egregium, stated for two patches over a common parameter domain, to be read as a statement about local isometries of surfaces.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 4, Section 4-3 (pp. 235-240)

import Definitions.Def_DoCarmo_surface_patch

namespace DoCarmoDG

theorem gauss_curvature_reparametrization_invariant
    (U V : Set (ℝ × ℝ)) (hU : IsOpen U) (hV : IsOpen V)
    (x y : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x) (hy : IsRegularPatch V y)
    (psi phi : ℝ × ℝ → ℝ × ℝ)
    (hpsi : ContDiffOn ℝ (⊤ : ℕ∞) psi U) (hphi : ContDiffOn ℝ (⊤ : ℕ∞) phi V)
    (hmaps : Set.MapsTo psi U V) (hmaps' : Set.MapsTo phi V U)
    (hleft : ∀ p ∈ U, phi (psi p) = p) (hright : ∀ q ∈ V, psi (phi q) = q)
    (hcomp : ∀ p ∈ U, x p.1 p.2 = y (psi p).1 (psi p).2) :
    ∀ p ∈ U, gaussCurvature x p.1 p.2 = gaussCurvature y (psi p).1 (psi p).2 := by sorry

end DoCarmoDG
