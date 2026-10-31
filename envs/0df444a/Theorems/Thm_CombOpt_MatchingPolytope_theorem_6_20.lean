-- Prove2me | Theorems.Thm_CombOpt_MatchingPolytope_theorem_6_20
-- name    : CombOpt.MatchingPolytope.theorem_6_20
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:06.977324+00:00
-- url     : https://prove2.me/theorems/63b4b984-840b-4e81-9b80-8f8892f577fe
-- title:
--   Theorem 6.20 (Matching Polytope Theorem, Edmonds) (corrected: loopless)
-- statement:
--   Let $G=(V,E)$ be a graph without loops (parallel edges allowed). Then the matching polytope $M(G)$, the convex hull of the characteristic vectors of the matchings of $G$, is the solution set of the system (6.7):
--   $$M(G)=\Bigl\{x\in\mathbb R^E:\ x(\delta(v))\le1\ (v\in V),\ \ x(\gamma(S))\le\tfrac{|S|-1}{2}\ (S\subseteq V,\ |S|\ge3 \text{ odd}),\ \ x_e\ge0\ (e\in E)\Bigr\}.$$
--
--   Edmonds' theorem (1965) gives a complete linear description of the matching polytope, so that maximum-weight matching is a linear program over (6.7); through LP duality it yields the min-max formula behind the weighted matching algorithm.
--
--   Differences from the source:
--   - correction: for any graph $G$ → $G$ loopless (parallel edges allowed); reason: counterexample: one node $v$ and one loop $e$ at $v$; every matching is $\emptyset$, so $M(G)=\{0\}$, but $e\notin\delta(v)$ and no $S$ has $|S|\ge3$, so (6.7) is $\{x_e\ge0\}$, which contains $x_e=5$
--   - encoding: conv.hull$(S)$ of a finite set, the set of convex combinations of $S$ (p. 199) → Mathlib's `convexHull ℝ S`; reason: for a finite set both are the set of convex combinations of finitely many points of $S$
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 6.20, p. 214 (PDF p. 222)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_Graph
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsLoopless
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsMatching
import Definitions.Def_CombOpt_MatchingPolytope_charVec
import Definitions.Def_CombOpt_MatchingPolytope_Graph_matchingPolytope
import Definitions.Def_CombOpt_MatchingPolytope_Graph_cut
import Definitions.Def_CombOpt_MatchingPolytope_Graph_gamma
import Definitions.Def_CombOpt_MatchingPolytope_Graph_system67

namespace CombOpt.MatchingPolytope

/-- **Theorem 6.20 (Matching Polytope Theorem, Edmonds 1965), corrected: loopless** —
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 6.20, p. 214 (PDF p. 222): "For any graph G = (V, E), the matching polytope is
defined by (6.7)." That is, `M(G)`, the convex hull of the characteristic vectors of the matchings
of `G`, equals the solution set of (6.7).

**Correction.** `G` is assumed loopless (parallel edges allowed). Counterexample to the printed
statement: `V = {v}`, `E = {e}` with `e` a loop at `v`. Every matching is `∅` (whichever way a
loop is counted, `M(G) ⊆ [0, 1]`), but `e ∉ δ(v)` and no `S` has `|S| ≥ 3`, so (6.7) is
`{x_e ≥ 0}`, which contains `x_e = 5`. -/
theorem theorem_6_20 {V E : Type*} [Fintype V] [Fintype E] (G : Graph V E)
    (hG : G.IsLoopless) :
    G.matchingPolytope = G.system67 := by sorry

end CombOpt.MatchingPolytope
