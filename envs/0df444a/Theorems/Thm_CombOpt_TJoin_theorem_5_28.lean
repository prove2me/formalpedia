-- Prove2me | Theorems.Thm_CombOpt_TJoin_theorem_5_28
-- name    : CombOpt.TJoin.theorem_5_28
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:07:30.005107+00:00
-- url     : https://prove2.me/theorems/2c1f41c5-e154-4977-86f4-0b4860c8f63c
-- title:
--   Theorem 5.28 — for $c\ge0$ the minimum cost of a $T$-join equals the optimum of the $T$-cut LP (5.33)
-- statement:
--   Let $G=(V,E)$ be a graph, $T\subseteq V$ with $|T|$ even, and $c\in\mathbb R^E$ with $c\ge0$. Then
--
--   $$\min\{c(J): J \text{ a } T\text{-join of } G\}=\min\Big\{\sum_{e\in E}c_ex_e:\ x(\delta(S))\ge1 \text{ for all } T\text{-odd } S\subseteq V,\ x\ge0\Big\}.$$
--
--   This is Edmonds and Johnson's theorem: for nonnegative costs the $T$-cut relaxation (5.33) is exact. With $T$ the odd-degree nodes it solves the Chinese postman problem by linear programming.
--
--   **Formalization Note** Both sides are taken in the extended reals; when $G$ has no $T$-join both are $+\infty$.
--
--   Differences from the source:
--   - encoding: the minimum cost of a T-join and the optimal value of (5.33) → infima in EReal (minTJoinCost, lpValue); reason: when a T-join exists the left side is a finite minimum and the LP value is its attained optimum; same instances
--   - reading: the statement presupposes that the minimum and the optimum exist → when G has no T-join both sides are ⊤, i.e. (5.33) is infeasible; reason: the book states the equality without existence hypotheses; the EReal reading covers that case and is the stronger one (paper.md, Readings recorded)
--   - encoding: for all T-cuts D → for all S ⊆ V with |S ∩ T| odd, the constraint on δ(S); reason: a T-cut is by definition δ(S) for a T-odd S; the same constraint set
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 5.28, p. 178 (PDF p. 186)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut
import Definitions.Def_CombOpt_TJoin_Graph_IsTJoin
import Definitions.Def_CombOpt_TJoin_Graph_minTJoinCost
import Definitions.Def_CombOpt_TJoin_Graph_IsFeasible533
import Definitions.Def_CombOpt_TJoin_Graph_lpValue533

namespace CombOpt.TJoin

open scoped symmDiff

/-- **Theorem 5.28 (Edmonds–Johnson: nonnegative costs).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 5.28, p. 178 (PDF p. 186): "If G = (V, E), T ⊆ V with |T| even, and c ∈ R^E with
c ≥ 0, then the minimum cost of a T-join of G is equal to the optimal value of (5.33)."

**Formalization Note.** Both values live in `EReal`. When `G` has a T-join, the left side is the
real minimum cost and the right side the optimal value of (5.33). When `G` has no T-join, the
left side is `⊤` and the statement says that (5.33) is infeasible. -/
theorem theorem_5_28 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (T : Finset V) (hT : Even T.card) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e) :
    G.minTJoinCost T c = G.lpValue533 T c := by sorry

end CombOpt.TJoin
