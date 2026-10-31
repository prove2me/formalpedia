-- Prove2me | Theorems.Thm_CombOpt_TutteBerge_proposition_5_4
-- name    : CombOpt.TutteBerge.proposition_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:09:49.367401+00:00
-- url     : https://prove2.me/theorems/9ea41847-0425-411e-b09d-4e4457ba7385
-- title:
--   Proposition 5.4 — extending a matching through a shrunk odd circuit
-- statement:
--   Let $C$ be an odd circuit of a finite graph $G$, let $G'=G\times C$, and let $M'$ be a matching of $G'$. Then there is a matching $M$ of $G$ such that
--   $$
--   M\subseteq M'\cup E(C)
--   $$
--   and the number of $M$-exposed nodes of $G$ equals the number of $M'$-exposed nodes of $G'$.
--
--   This is the elementary half of odd-circuit shrinking: a matching of the shrunk graph lifts to the original graph without losing any exposed-node count.
--
--   Differences from the source:
--   - reading: a matching is a set of edges such that no node is incident with more than one of them (p. 127) → IsMatching also requires that no edge of M is a loop; reason: the book's next sentences say M covers exactly 2|M| nodes and leaves |V| − 2|M| exposed, which fails for a loop
--   - encoding: |V|, |M|, |A| for finite sets → Nat.card V and Set.ncard, with binders [Finite V] [Finite E]; reason: these are the true cardinalities of finite sets
--   - encoding: the new node C of G × C; edges of G × C as edges of G → the node none of Option {v // v ∉ V(C)}; the subtype of edges outside γ(V(C)), with Subtype.val; reason: same graph; the book's edges keep their identity
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Proposition 5.4, p. 131 (PDF p. 139)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_IsMatching
import Definitions.Def_CombOpt_TutteBerge_Multigraph_exposedNodes
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_IsOddCircuit
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_nodeSet
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_edgeSet
import Definitions.Def_CombOpt_TutteBerge_Multigraph_edgesWithin
import Definitions.Def_CombOpt_TutteBerge_Multigraph_shrink

namespace CombOpt.TutteBerge

/-- **Proposition 5.4.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Proposition 5.4, p. 131 (PDF p. 139): "Let C be an odd circuit of G, let G′ = G × C, and let
M′ be a matching of G′. Then there is a matching M of G such that M ⊆ M′ ∪ E(C) and the number of
M-exposed nodes of G is the same as the number of M′-exposed nodes of G′."

`M′` is a set of edges of `G′`, which are edges of `G` by a subtype, so `Subtype.val '' M'` is `M′`
seen in `E`. -/
theorem proposition_5_4 {V E : Type*} [Finite V] [Finite E] (G : Multigraph V E) {x : V}
    (C : G.Path x x) (hC : C.IsOddCircuit) (M' : Set {e : E // e ∉ G.edgesWithin C.nodeSet})
    (hM' : (G.shrink C.nodeSet).IsMatching M') :
    ∃ M : Set E, G.IsMatching M ∧ M ⊆ (Subtype.val '' M') ∪ C.edgeSet ∧
      (G.exposedNodes M).ncard = ((G.shrink C.nodeSet).exposedNodes M').ncard := by sorry

end CombOpt.TutteBerge
