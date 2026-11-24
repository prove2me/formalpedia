-- Prove2me | Theorems.Thm_Arxiv1303_0923_theorem2_uniqueness_phaseless_scattered_field
-- name    : Arxiv1303_0923.theorem2_uniqueness_phaseless_scattered_field
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:33:07.930801+00:00
-- url     : https://prove2.me/theorems/48701384-4d54-41df-bbf1-e2724d621480
-- title:
--   Theorem 2: uniqueness for Inverse Problem 2 (phaseless scattered field, point sources on $S$)
-- statement:
--   Assume the standing setting of Section 1: bounded domains $\Omega\subset G_1\subset G$ in $\mathbb{R}^3$, $G_1$ convex with $C^1$ boundary $S$, and $\varepsilon\in(0,1)$ with $\operatorname{dist}(S,\partial G)>2\varepsilon$, $\operatorname{dist}(S,\partial\Omega)>2\varepsilon$. Let $q_1,q_2$ satisfy (3), (4) with $m=2$ and $q_1=q_2=q$ in $\mathbb{R}^3\setminus\Omega$. For $j=1,2$ and every source $x_0\in\mathbb{R}^3$ and real $k$, let $u_j(\cdot,x_0,k)$ be the solution of (5)-(7) with $q=q_j$, of the form (8), (9), and let $u_{s,j}=u_j-u_0$. Let $(a,b)$, $a<b$, be an interval. Assume moreover that $q(x)\neq0$ for all $x\in S$, and that
--   $$|u_{s,1}(x,x_0,k)|^2=|u_{s,2}(x,x_0,k)|^2\qquad\forall x_0\in S,\ \forall x\in B_\varepsilon(x_0),\ x\neq x_0,\ \forall k\in(a,b).$$
--   Then $q_1\equiv q_2$ on $\mathbb{R}^3$.
--
--   This is the version of Theorem 1 in which only the modulus of the scattered wave is measured.
--
--   **Formalization Note** The $\varepsilon$ is that of the standing setting. The proof's remark that $\varepsilon$ can be chosen small enough for (64) is not needed: since $q\ge0$ and $q(x_0)>0$, every segment from $x_0$ of positive length has a positive integral of $q$. The solutions $u_j$ enter as functions satisfying the defining conditions of (5)-(9) for every source and every real wavenumber; the $\delta$-source is encoded as described in the definitions.
-- source:
--   M. V. Klibanov, Phaseless inverse scattering problems in 3-d, arXiv:1303.0923v1 (2013), claim c003; Section 2, Theorem 2, eq. (12), PDF p. 4; proof in Section 4, pp. 13-14

import Mathlib
import Definitions.Def_Arxiv1303_0923_Basic

open MeasureTheory Filter Topology

namespace Arxiv1303_0923

theorem theorem2_uniqueness_phaseless_scattered_field (geo : Geometry) (q1 q2 q : R3 → ℝ)
    (hq1 : IsPotential geo.G 2 q1) (hq2 : IsPotential geo.G 2 q2)
    (h1 : ∀ x, x ∉ geo.Om → q1 x = q x) (h2 : ∀ x, x ∉ geo.Om → q2 x = q x)
    (hqS : ∀ x ∈ geo.S, q x ≠ 0)
    (u1 u2 : R3 → R3 → ℝ → ℂ)
    (hu1 : ∀ (x0 : R3) (k : ℝ), IsPointSourceSolution 2 q1 x0 k (fun x => u1 x x0 k))
    (hu2 : ∀ (x0 : R3) (k : ℝ), IsPointSourceSolution 2 q2 x0 k (fun x => u2 x x0 k))
    (a b : ℝ) (hab : a < b)
    (h12 : ∀ x0 ∈ geo.S, ∀ x ∈ Metric.ball x0 geo.eps, x ≠ x0 → ∀ k ∈ Set.Ioo a b,
      ‖u1 x x0 k - incWave x x0 k‖ ^ 2 = ‖u2 x x0 k - incWave x x0 k‖ ^ 2) :
    q1 = q2 := by sorry

end Arxiv1303_0923
