-- Prove2me | Theorems.Thm_CombOpt_TJoin_theorem_5_30
-- name    : CombOpt.TJoin.theorem_5_30
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:07:29.117553+00:00
-- url     : https://prove2.me/theorems/a51751ac-4090-49e4-b3d4-c208ebbf7198
-- title:
--   Theorem 5.30 — for arbitrary costs the minimum cost of a $T$-join equals the optimal value of (5.37)
-- statement:
--   Let $G=(V,E)$ be a graph (loops and parallel edges allowed), $T\subseteq V$ with $|T|$ even, and $c\in\mathbb R^E$ of arbitrary sign. Then the minimum cost of a $T$-join of $G$ equals the optimal value of the linear program
--
--   $$\begin{aligned}\text{minimize } &\sum_{e\in E}c_ex_e\\ \text{subject to } & x(\delta(S)\setminus F)-x(F)\ge1-|F| \text{ for all } S\subseteq V,\ F\subseteq\delta(S) \text{ with } |F|+|S\cap T| \text{ odd},\\ & 0\le x_e\le1 \text{ for all } e\in E.\end{aligned}\tag{5.37}$$
--
--   Equivalently, the polytope defined by (5.37) has the characteristic vectors of $T$-joins among its optimal solutions for every cost vector. It extends Theorem 5.28 to negative costs, where (5.33) is in general unbounded.
--
--   **Formalization Note** Both sides are taken in the extended reals; when $G$ has no $T$-join both are $+\infty$.
--
--   Differences from the source:
--   - encoding: the minimum cost of a T-join and the optimal value of (5.37) → infima in EReal (minTJoinCost, lpValue); reason: when a T-join exists the left side is a finite minimum and the LP value is its attained optimum; same instances
--   - reading: the statement presupposes that the minimum and the optimum exist → when G has no T-join both sides are ⊤, i.e. (5.37) is infeasible; reason: the book states the equality without existence hypotheses; the EReal reading covers that case and is the stronger one (paper.md, Readings recorded)
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 5.30, p. 180 (PDF p. 188)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut
import Definitions.Def_CombOpt_TJoin_Graph_IsTJoin
import Definitions.Def_CombOpt_TJoin_Graph_minTJoinCost
import Definitions.Def_CombOpt_TJoin_Graph_IsFeasible537
import Definitions.Def_CombOpt_TJoin_Graph_lpValue537

namespace CombOpt.TJoin

open scoped symmDiff

/-- **Theorem 5.30 (the T-join linear program for arbitrary costs).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 5.30, p. 180 (PDF p. 188): "If G = (V, E), T ⊆ V with |T| even, and c ∈ R^E, then
the minimum cost of a T-join of G is equal to the optimal value of (5.37)."

**Formalization Note.** Costs have arbitrary sign; loops and parallel edges are allowed. Both
values live in `EReal`. When `G` has a T-join, the left side is the real minimum cost and the
right side the optimal value of (5.37) (its feasible region is a nonempty polytope). When `G`
has no T-join, the left side is `⊤` and the statement says that (5.37) is infeasible. -/
theorem theorem_5_30 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (T : Finset V) (hT : Even T.card) (c : E → ℝ) :
    G.minTJoinCost T c = G.lpValue537 T c := by sorry

end CombOpt.TJoin
