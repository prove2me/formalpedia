-- Prove2me | Theorems.Thm_DoCarmoDG_theorema_egregium
-- name    : DoCarmoDG.theorema_egregium
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:17:20.048322+00:00
-- url     : https://prove2.me/theorems/17a9a4b7-2b17-4f93-bb25-ba87a63d1919
-- title:
--   Theorema Egregium (Gauss)
-- statement:
--   **Theorema Egregium** (Gauss; do Carmo §4-3, p. 237): *the Gaussian curvature $K$ of a surface is invariant by local isometries.*
--
--   In the parametrized formulation used here: if two regular patches $x$ and $y$ are defined on the same open set $U \subseteq \mathbb{R}^2$ and have the same first fundamental form, $E_x = E_y$, $F_x = F_y$, $G_x = G_y$ at every point of $U$, then their Gaussian curvatures agree at every point of $U$. Since a local isometry $\varphi$ between surfaces turns a parametrization $x$ of the first into the parametrization $y = \varphi \circ x$ of the second, with matching first fundamental forms, this is exactly do Carmo's statement; the milestone on invariance of $K$ under change of parameters supplies the remaining bookkeeping.
--
--   The content is that $K$, whose definition $K = (eg - f^2)/(EG - F^2)$ uses the second fundamental form and hence the way the surface sits in $\mathbb{R}^3$, is in fact determined by measurements made inside the surface.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 4, Section 4-3 (pp. 235-240)

import Definitions.Def_DoCarmo_surface_patch

namespace DoCarmoDG

theorem theorema_egregium
    (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (x y : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x) (hy : IsRegularPatch U y)
    (hE : ∀ p ∈ U, coeffE x p.1 p.2 = coeffE y p.1 p.2)
    (hF : ∀ p ∈ U, coeffF x p.1 p.2 = coeffF y p.1 p.2)
    (hG : ∀ p ∈ U, coeffG x p.1 p.2 = coeffG y p.1 p.2) :
    ∀ p ∈ U, gaussCurvature x p.1 p.2 = gaussCurvature y p.1 p.2 := by sorry

end DoCarmoDG
