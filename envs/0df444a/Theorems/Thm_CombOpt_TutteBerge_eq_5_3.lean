-- Prove2me | Theorems.Thm_CombOpt_TutteBerge_eq_5_3
-- name    : CombOpt.TutteBerge.eq_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:07:57.440682+00:00
-- url     : https://prove2.me/theorems/86986b6d-d06e-485d-b00a-ecd66d7b6e85
-- title:
--   (5.3), p. 133 — every node of an optimal $A$ is essential
-- statement:
--   Let $G=(V,E)$ be a finite graph, and let $A\subseteq V$ satisfy (5.1) with equality:
--   $$
--   \nu(G)=\tfrac12\bigl(|V|-\mathrm{oc}(G\setminus A)+|A|\bigr).
--   $$
--   Then every $v\in A$ is essential, that is, every maximum matching of $G$ covers $v$.
--
--   This links the sets attaining the Tutte–Berge bound to the structure of the maximum matchings.
--
--   Differences from the source:
--   - reading: a matching is a set of edges such that no node is incident with more than one of them (p. 127) → IsMatching also requires that no edge of M is a loop; reason: the book's next sentences say M covers exactly 2|M| nodes and leaves |V| − 2|M| exposed, which fails for a loop
--   - encoding: |V|, |M|, |A| for finite sets → Nat.card V and Set.ncard, with binders [Finite V] [Finite E]; reason: these are the true cardinalities of finite sets
--   - encoding: ½(·) and (|V(C)| − 1)/2 on integers → the expression in ℚ after casting every cardinal; reason: no truncation; the value of the book's expression
--   - encoding: oc(H), the number of odd components of H; G\A → odd connected components of H.toSimple (distinct nodes adjacent iff some edge joins them); G\A on the node and edge subtypes outside A; reason: loops and parallel edges do not change which nodes are joined by a path, so the components are the book's
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, (5.3), p. 133 (PDF p. 141)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_matchingNumber
import Definitions.Def_CombOpt_TutteBerge_Multigraph_tutteBergeBound
import Definitions.Def_CombOpt_TutteBerge_Multigraph_IsInessential

namespace CombOpt.TutteBerge

/-- **Statement (5.3).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), (5.3), p. 133 (PDF p. 141): "If A satisfies (5.1) with equality, then every v ∈ A is
essential."

A node is essential when it is not inessential (p. 132). -/
theorem eq_5_3 {V E : Type*} [Finite V] [Finite E] (G : Multigraph V E) (A : Set V)
    (hA : (G.matchingNumber : ℚ) = G.tutteBergeBound A) :
    ∀ v ∈ A, ¬ G.IsInessential v := by sorry

end CombOpt.TutteBerge
