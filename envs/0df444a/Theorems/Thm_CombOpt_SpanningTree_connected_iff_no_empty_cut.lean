-- Prove2me | Theorems.Thm_CombOpt_SpanningTree_connected_iff_no_empty_cut
-- name    : CombOpt.SpanningTree.connected_iff_no_empty_cut
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:03:45.059575+00:00
-- url     : https://prove2.me/theorems/31608c9a-7c6b-4f12-8d8a-c87dca8b2470
-- title:
--   Theorem 2.3 — a graph is connected iff no cut $\delta(A)$, $\emptyset\ne A\ne V$, is empty
-- statement:
--   A graph $G=(V,E)$ is connected if and only if there is no set $A\subseteq V$ with $\emptyset\ne A\ne V$ and
--   $$\delta(A)=\emptyset.$$
--
--   This is the basic characterization of connectivity by cuts, used to show that the greedy algorithms build a spanning tree.
--
--   **Formalization Note** No nonemptiness of $V$ is assumed; for $V=\emptyset$ both sides hold vacuously.
--
--   Differences from the source: none.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 2.3, p. 12 (PDF p. 21)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_SpanConnected
import Definitions.Def_CombOpt_SpanningTree_Graph_cut

namespace CombOpt.SpanningTree

/-- **Theorem 2.3: a graph is connected iff no cut δ(A) with ∅ ≠ A ≠ V is empty.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 2.3, p. 12 (PDF p. 21): "A graph G = (V, E) is connected if and only if there is no
set A ⊆ V, ∅ ≠ A ≠ V, with δ(A) = ∅."

`G` is connected (every two nodes are joined by a path) if and only if there is no node set `A`
with `A ≠ ∅`, `A ≠ V` and `δ(A) = ∅`.

**Formalization Note.** No nonemptiness of `V` is assumed: for `V = ∅` both sides hold
vacuously. -/
theorem connected_iff_no_empty_cut {V E : Type*} [Fintype V] [Fintype E] (G : Graph V E) :
    G.SpanConnected Finset.univ ↔
      ¬ ∃ A : Finset V, A.Nonempty ∧ A ≠ Finset.univ ∧ G.cut A = ∅ := by sorry

end CombOpt.SpanningTree
