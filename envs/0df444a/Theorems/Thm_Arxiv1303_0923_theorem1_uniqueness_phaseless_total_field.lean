-- Prove2me | Theorems.Thm_Arxiv1303_0923_theorem1_uniqueness_phaseless_total_field
-- name    : Arxiv1303_0923.theorem1_uniqueness_phaseless_total_field
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:32:20.101722+00:00
-- url     : https://prove2.me/theorems/000e7848-7cf5-4622-82ea-232f9cee2afd
-- title:
--   Theorem 1: uniqueness for Inverse Problem 1 (phaseless total field, point sources on $S$)
-- statement:
--   Assume the standing setting of Section 1: bounded domains $\Omega\subset G_1\subset G$ in $\mathbb{R}^3$, $G_1$ convex with $C^1$ boundary $S$, and $\varepsilon\in(0,1)$ with $\operatorname{dist}(S,\partial G)>2\varepsilon$, $\operatorname{dist}(S,\partial\Omega)>2\varepsilon$. Let $q_1,q_2$ satisfy (3), (4) with $m=2$ and $q_1=q_2=q$ in $\mathbb{R}^3\setminus\Omega$. For $j=1,2$ and every source $x_0\in\mathbb{R}^3$ and real $k$, let $u_j(\cdot,x_0,k)$ be the solution of (5)-(7) with $q=q_j$, of the form (8), (9), and let $u_{s,j}=u_j-u_0$. Let $(a,b)$, $a<b$, be an interval. Assume that
--   $$|u_1(x,x_0,k)|^2=|u_2(x,x_0,k)|^2\qquad\forall x_0\in S,\ \forall x\in B_\varepsilon(x_0),\ x\neq x_0,\ \forall k\in(a,b).$$
--   Then $q_1\equiv q_2$ on $\mathbb{R}^3$.
--
--   This is the first of the paper's four main results (Section 1.1, "One of main results"): a compactly supported nonnegative potential is uniquely determined by the modulus alone (no phase) of the total field of point sources on a convex surface, with receivers near each source and wavenumbers in an arbitrary interval.
--
--   **Formalization Note** The potential $q$ known outside $\Omega$ is a separate function equal to $q_1$ and $q_2$ there. The solutions $u_j$ enter as functions satisfying the defining conditions of (5)-(9) for every source and every real wavenumber; the $\delta$-source is encoded as described in the definitions.
-- source:
--   M. V. Klibanov, Phaseless inverse scattering problems in 3-d, arXiv:1303.0923v1 (2013), claim c001; Section 1.1, Theorem 1, eq. (10), PDF p. 2; proof in Section 3.3, pp. 9-13

import Mathlib
import Definitions.Def_Arxiv1303_0923_Basic

open MeasureTheory Filter Topology

namespace Arxiv1303_0923

theorem theorem1_uniqueness_phaseless_total_field (geo : Geometry) (q1 q2 q : R3 → ℝ)
    (hq1 : IsPotential geo.G 2 q1) (hq2 : IsPotential geo.G 2 q2)
    (h1 : ∀ x, x ∉ geo.Om → q1 x = q x) (h2 : ∀ x, x ∉ geo.Om → q2 x = q x)
    (u1 u2 : R3 → R3 → ℝ → ℂ)
    (hu1 : ∀ (x0 : R3) (k : ℝ), IsPointSourceSolution 2 q1 x0 k (fun x => u1 x x0 k))
    (hu2 : ∀ (x0 : R3) (k : ℝ), IsPointSourceSolution 2 q2 x0 k (fun x => u2 x x0 k))
    (a b : ℝ) (hab : a < b)
    (h10 : ∀ x0 ∈ geo.S, ∀ x ∈ Metric.ball x0 geo.eps, x ≠ x0 → ∀ k ∈ Set.Ioo a b,
      ‖u1 x x0 k‖ ^ 2 = ‖u2 x x0 k‖ ^ 2) :
    q1 = q2 := by sorry

end Arxiv1303_0923
