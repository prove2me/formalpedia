-- Prove2me | Theorems.Thm_Arxiv1303_0923_lemma2_total_field_finitely_many_zeros
-- name    : Arxiv1303_0923.lemma2_total_field_finitely_many_zeros
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:30:06.548162+00:00
-- url     : https://prove2.me/theorems/967cc961-8d08-4036-b763-02bf46cdcee9
-- title:
--   Lemma 2: the total field has finitely many zeros in $\mathbb{C}_+$
-- statement:
--   Assume the standing setting of Section 1: bounded domains $\Omega\subset G_1\subset G$ in $\mathbb{R}^3$, $G_1$ convex with $C^1$ boundary $S$, and $\varepsilon\in(0,1)$ with $\operatorname{dist}(S,\partial G)>2\varepsilon$, $\operatorname{dist}(S,\partial\Omega)>2\varepsilon$. Let $q$ satisfy (3), (4) with $m=2$, and for every source $x_0\in\mathbb{R}^3$ and every real $k$ let $u(\cdot,x_0,k)$ be the solution of (5)-(7) of the form (8), (9). Let $x_0\in\mathbb{R}^3$ and $x\in G$ with $x\neq x_0$. Then the analytic continuation of $k\mapsto u(x,x_0,k)$ has at most finitely many zeros in $\mathbb{C}_+=\{\operatorname{Im}k\ge0\}$:
--   $$\#\{k\in\mathbb{C}_+:\ u(x,x_0,k)=0\}<\infty .$$
--
--   The finiteness of these zeros is what allows the proof of Theorem 1 to divide them out with Blaschke-type factors.
--
--   **Formalization Note** The statement is made for every function $F$ holomorphic in some half-plane $\{\operatorname{Im}k>-\gamma\}$, $\gamma>0$, that equals $u(x,x_0,\cdot)$ on $\mathbb{R}$; by uniqueness of analytic continuation this is the continuation of Lemma 1.
-- source:
--   M. V. Klibanov, Phaseless inverse scattering problems in 3-d, arXiv:1303.0923v1 (2013), claim c007; Section 3.2, Lemma 2, PDF p. 8

import Mathlib
import Definitions.Def_Arxiv1303_0923_Basic

open MeasureTheory Filter Topology

namespace Arxiv1303_0923

theorem lemma2_total_field_finitely_many_zeros (geo : Geometry) (q : R3 → ℝ)
    (hq : IsPotential geo.G 2 q) (u : R3 → R3 → ℝ → ℂ)
    (hu : ∀ (x0 : R3) (k : ℝ), IsPointSourceSolution 2 q x0 k (fun x => u x x0 k))
    (x0 x : R3) (hx : x ∈ geo.G) (hxx0 : x ≠ x0) (γ : ℝ) (hγ : 0 < γ) (F : ℂ → ℂ)
    (hF : IsContinuation γ (u x x0) F) :
    {k : ℂ | k ∈ upperHalf ∧ F k = 0}.Finite := by sorry

end Arxiv1303_0923
