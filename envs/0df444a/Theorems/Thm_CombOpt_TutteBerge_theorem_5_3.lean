-- Prove2me | Theorems.Thm_CombOpt_TutteBerge_theorem_5_3
-- name    : CombOpt.TutteBerge.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:06:37.299986+00:00
-- url     : https://prove2.me/theorems/079b265f-8a6e-4ca3-8827-3e99ecf12dd7
-- title:
--   Theorem 5.3 — Tutte's Matching Theorem
-- statement:
--   A finite graph $G=(V,E)$ has a perfect matching if and only if
--   $$
--   \mathrm{oc}(G\setminus A)\le |A|\qquad\text{for every } A\subseteq V.
--   $$
--   The theorem characterizes the graphs with a perfect matching. The book derives it as an immediate consequence of Theorem 5.2.
--
--   **Formalization Note** The statement is on multigraphs. Its simple-graph form is Mathlib's `SimpleGraph.tutte` and the platform's `FamousTheorems.tutte_theorem`, which are not imported because their graph type is different.
--
--   Differences from the source:
--   - reading: a matching is a set of edges such that no node is incident with more than one of them (p. 127) → IsMatching also requires that no edge of M is a loop; reason: the book's next sentences say M covers exactly 2|M| nodes and leaves |V| − 2|M| exposed, which fails for a loop
--   - encoding: |V|, |M|, |A| for finite sets → Nat.card V and Set.ncard, with binders [Finite V] [Finite E]; reason: these are the true cardinalities of finite sets
--   - encoding: oc(H), the number of odd components of H; G\A → odd connected components of H.toSimple (distinct nodes adjacent iff some edge joins them); G\A on the node and edge subtypes outside A; reason: loops and parallel edges do not change which nodes are joined by a path, so the components are the book's
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 5.3, p. 131 (PDF p. 139)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_IsPerfectMatching
import Definitions.Def_CombOpt_TutteBerge_Multigraph_deleteNodes
import Definitions.Def_CombOpt_TutteBerge_Multigraph_oddComponentCount

namespace CombOpt.TutteBerge

/-- **Theorem 5.3 (Tutte's Matching Theorem).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 5.3, p. 131 (PDF p. 139): "A graph G = (V, E) has a perfect matching if and only if
for every subset A of nodes we have oc(G\A) ≤ |A|." -/
theorem theorem_5_3 {V E : Type*} [Finite V] [Finite E] (G : Multigraph V E) :
    (∃ M : Set E, G.IsPerfectMatching M) ↔
      ∀ A : Set V, (G.deleteNodes A).oddComponentCount ≤ A.ncard := by sorry

end CombOpt.TutteBerge
