-- Prove2me | Theorems.Thm_CombOpt_TJoin_proposition_5_25
-- name    : CombOpt.TJoin.proposition_5_25
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:06:53.048897+00:00
-- url     : https://prove2.me/theorems/e9996d67-a2be-4436-b5fc-db6740fdc149
-- title:
--   Proposition 5.25 — a minimal $T$-join is a union of $|T|/2$ edge-disjoint simple paths
-- statement:
--   Let $G=(V,E)$ be a graph and $T\subseteq V$ with $|T|$ even. Every **minimal** $T$-join $J$ (a $T$-join no proper subset of which is a $T$-join) is the union of the edge sets of $|T|/2$ edge-disjoint simple paths which join the nodes of $T$ in pairs:
--
--   $$J=P_1\cup\dots\cup P_{|T|/2},$$
--
--   where the $P_i$ are pairwise disjoint, $P_i$ is the edge set of a simple $(a_i,b_i)$-path, and $\{a_1,b_1\},\dots,\{a_{|T|/2},b_{|T|/2}\}$ partition $T$ into pairs.
--
--   This is the structural fact behind the reduction of the optimal $T$-join problem with nonnegative costs to a matching problem.
--
--   Differences from the source:
--   - encoding: the edge set of a simple path → a duplicate-free node list with an edge list joining consecutive nodes (IsSimplePath); pairs indexed by Fin (|T|/2); reason: the same paths and pairings
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Proposition 5.25, p. 169 (PDF p. 177)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut
import Definitions.Def_CombOpt_TJoin_Graph_IsTJoin
import Definitions.Def_CombOpt_TJoin_Graph_IsSimplePath
import Definitions.Def_CombOpt_TJoin_IsPairedPathUnion

namespace CombOpt.TJoin

open scoped symmDiff

/-- **Proposition 5.25 (minimal T-joins are unions of paths).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Proposition 5.25, p. 169 (PDF p. 177): "Every minimal T-join is the union of the
edge-sets of |T|/2 edge-disjoint simple paths, which join the nodes in T in pairs."

A minimal T-join is a T-join no proper subset of which is a T-join. -/
theorem proposition_5_25 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (T : Finset V) (hT : Even T.card) (J : Finset E)
    (hJ : G.IsTJoin T J) (hmin : ∀ J' : Finset E, J' ⊂ J → ¬ G.IsTJoin T J') :
    IsPairedPathUnion T J G.IsSimplePath := by sorry

end CombOpt.TJoin
