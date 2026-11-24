-- Prove2me | Theorems.Thm_Arxiv1303_0923_corollary1_phase_recovery_one_pair
-- name    : Arxiv1303_0923.corollary1_phase_recovery_one_pair
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:31:38.510642+00:00
-- url     : https://prove2.me/theorems/760f7c04-7c6e-4b27-bf91-069184f78c1d
-- title:
--   Corollary 1: one source-receiver pair recovers the complex total field
-- statement:
--   Assume the standing setting of Section 1: bounded domains $\Omega\subset G_1\subset G$ in $\mathbb{R}^3$, $G_1$ convex with $C^1$ boundary $S$, and $\varepsilon\in(0,1)$ with $\operatorname{dist}(S,\partial G)>2\varepsilon$, $\operatorname{dist}(S,\partial\Omega)>2\varepsilon$. Let $q_1,q_2$ satisfy (3), (4) with $m=2$ and $q_1=q_2=q$ in $\mathbb{R}^3\setminus\Omega$. For $j=1,2$ and every source $x_0\in\mathbb{R}^3$ and real $k$, let $u_j(\cdot,x_0,k)$ be the solution of (5)-(7) with $q=q_j$, of the form (8), (9), and let $u_{s,j}=u_j-u_0$. Let $(a,b)$, $a<b$, be an interval. Fix $y_0\in S$ and $y\in B_\varepsilon(y_0)$ with $y\neq y_0$, and assume
--   $$|u_1(y,y_0,k)|^2=|u_2(y,y_0,k)|^2\qquad\forall k\in(a,b).$$
--   Then $u_1(y,y_0,k)=u_2(y,y_0,k)$ for all $k\in\mathbb{R}$.
--
--   The modulus of the total field at one source-receiver pair on an interval of wavenumbers thus determines the complex field, phase included, at that pair for all real wavenumbers.
--
--   **Formalization Note** All conditions of Theorem 1 other than (10) are kept, as in the paper. The solutions $u_j$ enter as functions satisfying the defining conditions of (5)-(9) for every source and every real wavenumber; the $\delta$-source is encoded as described in the definitions.
-- source:
--   M. V. Klibanov, Phaseless inverse scattering problems in 3-d, arXiv:1303.0923v1 (2013), claim c002; Section 1.1, Corollary 1, eq. (11), PDF p. 2; Remark 1, p. 3

import Mathlib
import Definitions.Def_Arxiv1303_0923_Basic

open MeasureTheory Filter Topology

namespace Arxiv1303_0923

theorem corollary1_phase_recovery_one_pair (geo : Geometry) (q1 q2 q : R3 → ℝ)
    (hq1 : IsPotential geo.G 2 q1) (hq2 : IsPotential geo.G 2 q2)
    (h1 : ∀ x, x ∉ geo.Om → q1 x = q x) (h2 : ∀ x, x ∉ geo.Om → q2 x = q x)
    (u1 u2 : R3 → R3 → ℝ → ℂ)
    (hu1 : ∀ (x0 : R3) (k : ℝ), IsPointSourceSolution 2 q1 x0 k (fun x => u1 x x0 k))
    (hu2 : ∀ (x0 : R3) (k : ℝ), IsPointSourceSolution 2 q2 x0 k (fun x => u2 x x0 k))
    (a b : ℝ) (hab : a < b) (y0 y : R3) (hy0 : y0 ∈ geo.S) (hy : y ∈ Metric.ball y0 geo.eps)
    (hyy0 : y ≠ y0)
    (h11 : ∀ k ∈ Set.Ioo a b, ‖u1 y y0 k‖ ^ 2 = ‖u2 y y0 k‖ ^ 2) :
    ∀ k : ℝ, u1 y y0 k = u2 y y0 k := by sorry

end Arxiv1303_0923
