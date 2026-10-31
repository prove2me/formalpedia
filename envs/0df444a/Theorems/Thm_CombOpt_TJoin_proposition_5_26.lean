-- Prove2me | Theorems.Thm_CombOpt_TJoin_proposition_5_26
-- name    : CombOpt.TJoin.proposition_5_26
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:06:33.283036+00:00
-- url     : https://prove2.me/theorems/998b417f-cb0a-41a4-8794-3c94397cddab
-- title:
--   Proposition 5.26 — for $c\ge0$ some optimal $T$-join is a union of $|T|/2$ edge-disjoint shortest paths
-- statement:
--   Let $G=(V,E)$ be a graph, $T\subseteq V$ with $|T|$ even, and $c\in\mathbb R^E$ with $c\ge0$, and suppose $G$ has a $T$-join. Then there is an optimal $T$-join $J$ (one with $c(J)\le c(J')$ for every $T$-join $J'$) that is the union of the edge sets of $|T|/2$ edge-disjoint shortest paths joining the nodes of $T$ in pairs:
--
--   $$J=P_1\cup\dots\cup P_{|T|/2},$$
--
--   the $P_i$ pairwise disjoint, $P_i$ the edge set of a least-cost simple $(a_i,b_i)$-path, and the pairs $\{a_i,b_i\}$ partitioning $T$.
--
--   Consequently, an optimal $T$-join for nonnegative costs is found by a minimum-weight perfect matching on $T$ with shortest-path distances as weights.
--
--   Differences from the source:
--   - reading: there is an optimal T-join → hypothesis: G has a T-join; reason: an optimal T-join exists only if some T-join exists; the book's sentence presupposes it
--   - reading: shortest paths → simple paths of least cost among simple paths with the same ends; reason: the paths are those of Proposition 5.25, which are simple; for c ≥ 0 the least cost over simple paths equals the least cost over all paths
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Proposition 5.26, p. 169 (PDF p. 177)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut
import Definitions.Def_CombOpt_TJoin_Graph_IsTJoin
import Definitions.Def_CombOpt_TJoin_Graph_IsSimplePath
import Definitions.Def_CombOpt_TJoin_Graph_IsShortestPath
import Definitions.Def_CombOpt_TJoin_IsPairedPathUnion

namespace CombOpt.TJoin

open scoped symmDiff

/-- **Proposition 5.26 (an optimal T-join made of shortest paths).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Proposition 5.26, p. 169 (PDF p. 177): "Suppose that c ≥ 0. Then there is an optimal
T-join that is the union of |T|/2 edge-disjoint shortest paths joining the nodes of T in pairs."

**Formalization Note.** An optimal T-join exists only if some T-join exists, so that is a
hypothesis. Each path is a simple path of least cost among the simple paths between its ends;
for `c ≥ 0` this is least cost among all paths. -/
theorem proposition_5_26 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (T : Finset V) (hT : Even T.card) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (hex : ∃ J : Finset E, G.IsTJoin T J) :
    ∃ J : Finset E, G.IsTJoin T J ∧
      (∀ J' : Finset E, G.IsTJoin T J' → ∑ e ∈ J, c e ≤ ∑ e ∈ J', c e) ∧
      IsPairedPathUnion T J (G.IsShortestPath c) := by sorry

end CombOpt.TJoin
