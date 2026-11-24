-- Prove2me | Theorems.Thm_Arxiv1303_0923_theorem4_uniqueness_phaseless_scattered_distributed_source
-- name    : Arxiv1303_0923.theorem4_uniqueness_phaseless_scattered_distributed_source
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:35:58.262925+00:00
-- url     : https://prove2.me/theorems/8bc211fa-dac5-43df-bcd1-acc4b3e641b6
-- title:
--   Theorem 4: uniqueness for Inverse Problem 4 (phaseless scattered field of a distributed source, data on $S$)
-- statement:
--   Assume the standing setting of Section 1: bounded domains $\Omega\subset G_1\subset G$ in $\mathbb{R}^3$, $G_1$ convex with $C^1$ boundary $S$, and $\varepsilon\in(0,1)$ with $\operatorname{dist}(S,\partial G)>2\varepsilon$, $\operatorname{dist}(S,\partial\Omega)>2\varepsilon$. Let $g$ satisfy (13), (14). Let $q_1,q_2$ satisfy (3), (4) with $m=4$ and $q_1=q_2=q$ in $\mathbb{R}^3\setminus\Omega$. For $j=1,2$ and every real $k$ let $v_j(\cdot,k)\in C^5(\mathbb{R}^3)$ be the solution of (15)-(17) with $q=q_j$, and let $v_{s,j}=v_j-v_0$. Let $(a,b)$, $a<b$, be an interval. Assume moreover that $q(x)\neq0$ for all $x\in S$, and that
--   $$|v_{s,1}(x,k)|^2=|v_{s,2}(x,k)|^2\qquad\forall x\in S,\ \forall k\in(a,b).$$
--   Then $q_1\equiv q_2$ on $\mathbb{R}^3$.
--
--   This is the version of Theorem 3 in which only the modulus of the scattered wave $v_s=v-v_0$ is measured.
--
--   **Formalization Note** $v_0$ is given by its integral formula over $G$.
-- source:
--   M. V. Klibanov, Phaseless inverse scattering problems in 3-d, arXiv:1303.0923v1 (2013), claim c005; Section 2, Theorem 4, eq. (20), PDF p. 6; proof in Section 5.3, p. 18

import Mathlib
import Definitions.Def_Arxiv1303_0923_Basic

open MeasureTheory Filter Topology

namespace Arxiv1303_0923

theorem theorem4_uniqueness_phaseless_scattered_distributed_source (geo : Geometry)
    (g : R3 → ℝ) (hg : IsSourceTerm geo g) (q1 q2 q : R3 → ℝ)
    (hq1 : IsPotential geo.G 4 q1) (hq2 : IsPotential geo.G 4 q2)
    (h1 : ∀ x, x ∉ geo.Om → q1 x = q x) (h2 : ∀ x, x ∉ geo.Om → q2 x = q x)
    (hqS : ∀ x ∈ geo.S, q x ≠ 0)
    (v1 v2 : R3 → ℝ → ℂ)
    (hv1 : ∀ k : ℝ, IsSourceSolution q1 g k (fun x => v1 x k))
    (hv2 : ∀ k : ℝ, IsSourceSolution q2 g k (fun x => v2 x k))
    (a b : ℝ) (hab : a < b)
    (h20 : ∀ x ∈ geo.S, ∀ k ∈ Set.Ioo a b,
      ‖v1 x k - bgField geo.G g x k‖ ^ 2 = ‖v2 x k - bgField geo.G g x k‖ ^ 2) :
    q1 = q2 := by sorry

end Arxiv1303_0923
