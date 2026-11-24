-- Prove2me | Theorems.Thm_Arxiv1303_0923_theorem3_uniqueness_phaseless_distributed_source
-- name    : Arxiv1303_0923.theorem3_uniqueness_phaseless_distributed_source
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:35:03.23682+00:00
-- url     : https://prove2.me/theorems/9cba6442-7348-43c8-8223-d32081ef4a2c
-- title:
--   Theorem 3: uniqueness for Inverse Problem 3 (phaseless total field of a distributed source, data on $S$)
-- statement:
--   Assume the standing setting of Section 1: bounded domains $\Omega\subset G_1\subset G$ in $\mathbb{R}^3$, $G_1$ convex with $C^1$ boundary $S$, and $\varepsilon\in(0,1)$ with $\operatorname{dist}(S,\partial G)>2\varepsilon$, $\operatorname{dist}(S,\partial\Omega)>2\varepsilon$. Let $g$ satisfy (13), (14). Let $q_1,q_2$ satisfy (3), (4) with $m=4$ and $q_1=q_2=q$ in $\mathbb{R}^3\setminus\Omega$. For $j=1,2$ and every real $k$ let $v_j(\cdot,k)\in C^5(\mathbb{R}^3)$ be the solution of (15)-(17) with $q=q_j$, and let $v_{s,j}=v_j-v_0$. Let $(a,b)$, $a<b$, be an interval. Assume that
--   $$|v_1(x,k)|^2=|v_2(x,k)|^2\qquad\forall x\in S,\ \forall k\in(a,b).$$
--   Then $q_1\equiv q_2$ on $\mathbb{R}^3$.
--
--   Here the data depend on three variables, a point of the surface $S$ and the wavenumber, the same number as the unknown $q$. So unlike Theorems 1 and 2 this is a uniqueness theorem for data that are not over-determined.
--
--   **Formalization Note** The solutions $v_j$ enter as functions satisfying (15)-(17) with $q=q_j$ for every real $k$.
-- source:
--   M. V. Klibanov, Phaseless inverse scattering problems in 3-d, arXiv:1303.0923v1 (2013), claim c004; Section 2, Theorem 3, eq. (19), PDF pp. 5-6; proof in Section 5.2, pp. 16-18

import Mathlib
import Definitions.Def_Arxiv1303_0923_Basic

open MeasureTheory Filter Topology

namespace Arxiv1303_0923

theorem theorem3_uniqueness_phaseless_distributed_source (geo : Geometry) (g : R3 → ℝ)
    (hg : IsSourceTerm geo g) (q1 q2 q : R3 → ℝ)
    (hq1 : IsPotential geo.G 4 q1) (hq2 : IsPotential geo.G 4 q2)
    (h1 : ∀ x, x ∉ geo.Om → q1 x = q x) (h2 : ∀ x, x ∉ geo.Om → q2 x = q x)
    (v1 v2 : R3 → ℝ → ℂ)
    (hv1 : ∀ k : ℝ, IsSourceSolution q1 g k (fun x => v1 x k))
    (hv2 : ∀ k : ℝ, IsSourceSolution q2 g k (fun x => v2 x k))
    (a b : ℝ) (hab : a < b)
    (h19 : ∀ x ∈ geo.S, ∀ k ∈ Set.Ioo a b, ‖v1 x k‖ ^ 2 = ‖v2 x k‖ ^ 2) :
    q1 = q2 := by sorry

end Arxiv1303_0923
