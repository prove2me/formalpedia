-- Prove2me | Theorems.Thm_CombOpt_MatchingPolytope_theorem_6_3
-- name    : CombOpt.MatchingPolytope.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:07:48.531354+00:00
-- url     : https://prove2.me/theorems/816d7a60-d9f1-4905-8e55-b5216a2d69f2
-- title:
--   Theorem 6.3 (Perfect Matching Polytope Theorem) (corrected: loopless)
-- statement:
--   Let $G=(V,E)$ be a graph without loops (parallel edges allowed), and let $\mathcal{PM}(G)\subseteq\mathbb R^E$ be the set of characteristic vectors of its perfect matchings. Then
--   $$\operatorname{conv.hull}(\mathcal{PM}(G))=\{x\in\mathbb R^E:\ x \text{ satisfies } (6.3)\},$$
--   where (6.3) is the system
--   $$\begin{aligned} x(\delta(v))&=1, && v\in V,\\ x(\delta(S))&\ge1, && S\subseteq V,\ |S|\ge3 \text{ odd},\\ x_e&\ge0, && e\in E.\end{aligned}$$
--
--   This is Edmonds' description of the perfect matching polytope; it is the first instance in the chapter of a linear description of the convex hull of a combinatorial family.
--
--   **Formalization Note** When $G$ has no perfect matching, both sides are empty. The proved platform theorem `OAI.MatchingEntropy.LooplessGraph.constraint_subset_polytope_aux` is the inclusion "$\supseteq$" for an even number of nodes, in another vocabulary.
--
--   Differences from the source:
--   - correction: for any graph $G$ → $G$ loopless (parallel edges allowed); reason: counterexample: nodes $a,b$, an edge $f=ab$ and a loop $\ell$ at $a$; the only perfect matching is $\{f\}$, so the hull has $x_\ell=0$, but $\ell$ lies in no cut and no $S$ has $|S|\ge3$, so $x_f=1,x_\ell=5$ solves (6.3)
--   - encoding: conv.hull$(S)$ of a finite set, the set of convex combinations of $S$ (p. 199) → Mathlib's `convexHull ℝ S`; reason: for a finite set both are the set of convex combinations of finitely many points of $S$
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 6.3, p. 201 (PDF p. 209)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_Graph
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsLoopless
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsMatching
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsPerfectMatching
import Definitions.Def_CombOpt_MatchingPolytope_charVec
import Definitions.Def_CombOpt_MatchingPolytope_Graph_cut
import Definitions.Def_CombOpt_MatchingPolytope_Graph_system63

namespace CombOpt.MatchingPolytope

/-- **Theorem 6.3 (Perfect Matching Polytope Theorem), corrected: loopless** —
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 6.3, p. 201 (PDF p. 209): "For any graph G = (V, E), the convex hull of PM(G) is
identical to the set of solutions of the linear system (6.3)." `PM(G)` is the set of
characteristic vectors of perfect matchings of `G`.

**Correction.** `G` is assumed loopless (parallel edges allowed). Counterexample to the printed
statement: `V = {a, b}`, `E = {f, ℓ}` with `f` joining `a` and `b` and `ℓ` a loop at `a`. The
only perfect matching is `{f}`, so the hull is `{χ_{f}}`, with `x_ℓ = 0`; but `ℓ` lies in no cut
and no `S` has `|S| ≥ 3`, so `x_f = 1, x_ℓ = 5` solves (6.3). -/
theorem theorem_6_3 {V E : Type*} [Fintype V] [Fintype E] (G : Graph V E)
    (hG : G.IsLoopless) :
    convexHull ℝ {x | ∃ M : Finset E, G.IsPerfectMatching M ∧ x = charVec M} = G.system63 := by sorry

end CombOpt.MatchingPolytope
