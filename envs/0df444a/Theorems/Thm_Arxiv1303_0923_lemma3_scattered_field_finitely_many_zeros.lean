-- Prove2me | Theorems.Thm_Arxiv1303_0923_lemma3_scattered_field_finitely_many_zeros
-- name    : Arxiv1303_0923.lemma3_scattered_field_finitely_many_zeros
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:30:36.779464+00:00
-- url     : https://prove2.me/theorems/606394bf-eac3-44ad-ab30-9a215be91856
-- title:
--   Lemma 3: the scattered field has finitely many zeros in $\mathbb{C}_+$ when $\int_{L(x,x_0)}q\,ds\neq0$
-- statement:
--   Assume the standing setting of Section 1: bounded domains $\Omega\subset G_1\subset G$ in $\mathbb{R}^3$, $G_1$ convex with $C^1$ boundary $S$, and $\varepsilon\in(0,1)$ with $\operatorname{dist}(S,\partial G)>2\varepsilon$, $\operatorname{dist}(S,\partial\Omega)>2\varepsilon$. Let $q$ satisfy (3), (4) with $m=2$, and for every source $x_0\in\mathbb{R}^3$ and every real $k$ let $u(\cdot,x_0,k)$ be the solution of (5)-(7) of the form (8), (9). Let $x_0\in\mathbb{R}^3$ and $x\in G$ be such that
--   $$\int_{L(x,x_0)}q(\xi)\,ds\neq0 .$$
--   Then the analytic continuation of $k\mapsto u_s(x,x_0,k)=u(x,x_0,k)-u_0(x,x_0,k)$ has at most finitely many zeros in $\mathbb{C}_+$.
--
--   This is the counterpart of Lemma 2 for the scattered wave and is used in the proof of Theorem 2.
--
--   **Formalization Note** As in Lemma 2, the statement is made for every holomorphic function on a half-plane $\{\operatorname{Im}k>-\gamma\}$, $\gamma>0$, that equals $u_s(x,x_0,\cdot)$ on $\mathbb{R}$. The hypothesis on the line integral forces $x\neq x_0$.
-- source:
--   M. V. Klibanov, Phaseless inverse scattering problems in 3-d, arXiv:1303.0923v1 (2013), claim c008; Section 3.2, Lemma 3, PDF pp. 8-9

import Mathlib
import Definitions.Def_Arxiv1303_0923_Basic

open MeasureTheory Filter Topology

namespace Arxiv1303_0923

theorem lemma3_scattered_field_finitely_many_zeros (geo : Geometry) (q : R3 → ℝ)
    (hq : IsPotential geo.G 2 q) (u : R3 → R3 → ℝ → ℂ)
    (hu : ∀ (x0 : R3) (k : ℝ), IsPointSourceSolution 2 q x0 k (fun x => u x x0 k))
    (x0 x : R3) (hx : x ∈ geo.G) (hL : segInt q x x0 ≠ 0) (γ : ℝ) (hγ : 0 < γ) (F : ℂ → ℂ)
    (hF : IsContinuation γ (fun k : ℝ => u x x0 k - incWave x x0 k) F) :
    {k : ℂ | k ∈ upperHalf ∧ F k = 0}.Finite := by sorry

end Arxiv1303_0923
