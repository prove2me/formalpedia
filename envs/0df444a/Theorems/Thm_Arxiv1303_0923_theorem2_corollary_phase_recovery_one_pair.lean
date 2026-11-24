-- Prove2me | Theorems.Thm_Arxiv1303_0923_theorem2_corollary_phase_recovery_one_pair
-- name    : Arxiv1303_0923.theorem2_corollary_phase_recovery_one_pair
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:32:47.993373+00:00
-- url     : https://prove2.me/theorems/8a44d4fc-2259-440b-9b35-823155bb65a7
-- title:
--   Remark 1 (corollary of Theorem 2, eq. (67)): one source-receiver pair recovers the complex scattered field
-- statement:
--   Assume the standing setting of Section 1: bounded domains $\Omega\subset G_1\subset G$ in $\mathbb{R}^3$, $G_1$ convex with $C^1$ boundary $S$, and $\varepsilon\in(0,1)$ with $\operatorname{dist}(S,\partial G)>2\varepsilon$, $\operatorname{dist}(S,\partial\Omega)>2\varepsilon$. Let $q_1,q_2$ satisfy (3), (4) with $m=2$ and $q_1=q_2=q$ in $\mathbb{R}^3\setminus\Omega$. For $j=1,2$ and every source $x_0\in\mathbb{R}^3$ and real $k$, let $u_j(\cdot,x_0,k)$ be the solution of (5)-(7) with $q=q_j$, of the form (8), (9), and let $u_{s,j}=u_j-u_0$. Let $(a,b)$, $a<b$, be an interval. Assume moreover that $q(x)\neq0$ for all $x\in S$. Fix $x_0\in S$ and $x\in B_\varepsilon(x_0)$ with $x\neq x_0$, and assume
--   $$|u_{s,1}(x,x_0,k)|^2=|u_{s,2}(x,x_0,k)|^2\qquad\forall k\in(a,b).$$
--   Then $u_{s,1}(x,x_0,k)=u_{s,2}(x,x_0,k)$ for all $k\in\mathbb{R}$.
--
--   This is the corollary of Theorem 2 announced in Remark 1, proved as eq. (67): the modulus of the scattered wave at one pair determines the complex scattered wave at that pair.
--
--   **Formalization Note** The paper does not write this corollary out. The hypotheses are those of Theorem 2 with (12) replaced by data at one pair, as Remark 1 says. The condition (64) at the pair, $\int_{L(x,x_0)}q\,ds\neq0$, is not added as a hypothesis because it follows from $q\ge0$ and $q(x_0)\neq0$. The solutions $u_j$ enter as functions satisfying the defining conditions of (5)-(9) for every source and every real wavenumber; the $\delta$-source is encoded as described in the definitions.
-- source:
--   M. V. Klibanov, Phaseless inverse scattering problems in 3-d, arXiv:1303.0923v1 (2013), claim c013; Section 1.1, Remark 1, PDF p. 3; proved as eq. (67) in Section 4, pp. 13-14

import Mathlib
import Definitions.Def_Arxiv1303_0923_Basic

open MeasureTheory Filter Topology

namespace Arxiv1303_0923

theorem theorem2_corollary_phase_recovery_one_pair (geo : Geometry) (q1 q2 q : R3 → ℝ)
    (hq1 : IsPotential geo.G 2 q1) (hq2 : IsPotential geo.G 2 q2)
    (h1 : ∀ x, x ∉ geo.Om → q1 x = q x) (h2 : ∀ x, x ∉ geo.Om → q2 x = q x)
    (hqS : ∀ x ∈ geo.S, q x ≠ 0)
    (u1 u2 : R3 → R3 → ℝ → ℂ)
    (hu1 : ∀ (x0 : R3) (k : ℝ), IsPointSourceSolution 2 q1 x0 k (fun x => u1 x x0 k))
    (hu2 : ∀ (x0 : R3) (k : ℝ), IsPointSourceSolution 2 q2 x0 k (fun x => u2 x x0 k))
    (a b : ℝ) (hab : a < b) (x0 x : R3) (hx0 : x0 ∈ geo.S) (hx : x ∈ Metric.ball x0 geo.eps)
    (hxx0 : x ≠ x0)
    (hdata : ∀ k ∈ Set.Ioo a b,
      ‖u1 x x0 k - incWave x x0 k‖ ^ 2 = ‖u2 x x0 k - incWave x x0 k‖ ^ 2) :
    ∀ k : ℝ, u1 x x0 k - incWave x x0 k = u2 x x0 k - incWave x x0 k := by sorry

end Arxiv1303_0923
