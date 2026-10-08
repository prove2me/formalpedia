-- Prove2me | Theorems.Thm_EDPHardness_IntegralityGap_theorem_5_integrality_gap
-- name    : EDPHardness.IntegralityGap.theorem_5_integrality_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:01.456986+00:00
-- url     : https://prove2.me/theorems/99ef1a76-536b-4971-b517-38fc33a4c3f9
-- title:
--   Theorem 5 (EDPwC) — the flow relaxation has integrality gap ≥ β₁/(4c) against integral routings of congestion c − 1
-- statement:
--   For a $c$-uniform hypergraph $H$ on $n$ vertices with $m=\lfloor\beta_2 n\rfloor$ hyperedges let $G(H)$ be the edge-disjoint-paths instance of the mission: vertices $s(v),t(v)$ for every vertex $v$ and $\ell_i,r_i$ for every hyperedge, special edges $(\ell_i,r_i)$, regular edges along the hyperedges containing each $v$ in increasing order, and pairs $(s(v),t(v))$. Here
--   $$\beta_1=\frac14\Big(\frac{\log n}{150(\log\log n)^2}\Big)^{1/c},\qquad\beta_2=6(2\beta_1)^{c-1}\ln\beta_1,$$
--   with $\log$ to base $2$ and $\ln$ natural.
--
--   There are absolute constants $\alpha>0$ and $N_0$ such that for every $n\ge N_0$ and every integer $c$ with
--   $$2\le c\le\alpha\,\frac{\log\log n}{\log\log\log n}$$
--   there is a hypergraph $H$ as above for which
--   1. the multicommodity flow relaxation of $G(H)$ has a feasible fractional solution (capacity $1$ on every edge) of value $n/c$, and
--   2. every integral routing in $G(H)$ in which every edge carries at most $c-1$ paths routes at most $4n/\beta_1$ pairs.
--
--   Hence the integrality gap of the relaxation on $G(H)$, against integral solutions of congestion $c-1$, is at least
--   $$\frac{n/c}{4n/\beta_1}=\frac{\beta_1}{4c}=\Omega\Big(\frac1c\Big(\frac{\log n}{(\log\log n)^2}\Big)^{1/c}\Big).$$
--   Since $G(H)$ has $2n+2m=O(n\log n)$ vertices, this is the EDPwC part of Theorem 5 of the paper, there written for congestion $c-1$ in terms of the number $V$ of vertices.
--
--   **Formalization Note** The theorem is stated in the explicit form Section 2 proves, in the hyperedge size $c$ (the integral congestion is $c-1$); the $O(\cdot)$ bound on $c$ and "sufficiently large $n$" are the absolute constants $\alpha$ and $N_0$, chosen before $n$ and $c$. The instance is required to be $G(H)$ for a hypergraph with exactly $\lfloor\beta_2n\rfloor$ hyperedges of size $c$ on $n$ vertices. The ANFwC part of Theorem 5 and its superconstant remark are not formalized.
-- source:
--   Andrews, Chuzhoy, Guruswami, Khanna, Talwar, Zhang, Inapproximability of Edge-Disjoint Paths and Low Congestion Routing on Undirected Graphs, Combinatorica 30 (2010), p. 489, Theorem 5 (EDPwC part), in the explicit form of Section 2, pp. 491 and 495–496

import Mathlib
import Definitions.Def_EDPHardness_IntegralityGap_FlowRelaxation
import Definitions.Def_EDPHardness_IntegralityGap_GapInstance

namespace EDPHardness.IntegralityGap

theorem theorem_5_integrality_gap :
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ c : ℕ, 2 ≤ c →
      (c : ℝ) ≤ α * Real.logb 2 (Real.logb 2 n) / Real.logb 2 (Real.logb 2 (Real.logb 2 n)) →
      ∃ H : Hyp n (numEdges n c) c,
        (∃ F : FracSol (gapGraph H) (src n (numEdges n c)) (snk n (numEdges n c)),
          F.value = (n : ℝ) / c) ∧
        ∀ R : IntRouting (gapGraph H) (src n (numEdges n c)) (snk n (numEdges n c)) (c - 1),
          (R.routed.card : ℝ) ≤ 4 * (n : ℝ) / beta1 n c := by sorry

end EDPHardness.IntegralityGap
