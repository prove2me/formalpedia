-- Prove2me | Theorems.Thm_CarrollGR_spherical_coordinates_minkowski
-- name    : CarrollGR.spherical_coordinates_minkowski
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T23:49:28.42891+00:00
-- url     : https://prove2.me/theorems/7249f9fa-4811-411e-8d7c-984f08d90c60
-- title:
--   Minkowski metric in spherical coordinates
-- statement:
--   Let $\Phi(t,r,\theta,\phi)=(t,\;r\sin\theta\cos\phi,\;r\sin\theta\sin\phi,\;r\cos\theta)$ be the change to spherical coordinates on space, and let $J=\partial\Phi^a/\partial x^\mu$ be its Jacobian matrix at a point $x=(t,r,\theta,\phi)$. Then the components of the Minkowski metric $\eta=\operatorname{diag}(-1,1,1,1)$ in the new coordinates are
--
--   $$J^{\mathsf T}\,\eta\,J=\begin{pmatrix}-1&0&0&0\\0&1&0&0\\0&0&r^2&0\\0&0&0&r^2\sin^2\theta\end{pmatrix},$$
--
--   that is, $ds^2=-dt^2+dr^2+r^2d\theta^2+r^2\sin^2\theta\,d\phi^2$.
--
--   This is Carroll's example showing that a flat metric can have non-constant components in non-Cartesian coordinates, and it provides the angular part of every spherically symmetric metric used later.
--
--   **Formalization Note** The right-hand side is `sphericalMetric` with $A=B=1$. The identity is claimed at every point, including $r=0$ and $\sin\theta=0$, where both sides are still defined.
-- source:
--   S. M. Carroll, "A No-Nonsense Introduction to General Relativity" (lecture notes, 2001), uploaded PDF, p. 7, eqs. (18)–(20)

import Mathlib
import Definitions.Def_CarrollGR_Defs

open scoped ContDiff

namespace CarrollGR

theorem spherical_coordinates_minkowski (x : Coord) :
    (jacobian sphericalToCartesian x).transpose * minkowskiEta * jacobian sphericalToCartesian x
      = sphericalMetric (fun _ _ => 1) (fun _ _ => 1) x := by sorry

end CarrollGR
