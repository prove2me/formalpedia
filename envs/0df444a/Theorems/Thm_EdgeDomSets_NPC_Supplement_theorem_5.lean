-- Prove2me | Theorems.Thm_EdgeDomSets_NPC_Supplement_theorem_5
-- name    : EdgeDomSets.NPC.Supplement.theorem_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T11:14:26.577102+00:00
-- url     : https://prove2.me/theorems/89224b05-599e-4b2a-9cb5-ab514ac4b82c
-- title:
--   THEOREM 5, p. 370 — trees exactly when the total graph is chordal
-- statement:
--   Let $G$ be a connected finite simple graph. Then
--
--   $$
--   G\text{ is a tree}\quad\Longleftrightarrow\quad T(G)\text{ is chordal}.
--   $$
--
--   Here chordal means that every simple cycle with at least four vertices has an edge joining nonconsecutive cycle vertices. This companion theorem identifies the total graphs relevant to the tree setting of §4.
--
--   **Formalization Note** Mathlib's `Connected` includes a vertex, and `IsTree` is connectedness plus acyclicity. The published cycle-and-chord predicate is reused without additional restrictions. The one-vertex graph is included.
--
--   Differences from the source:
--   - encoding: a connected finite graph is a tree iff its total graph is chordal → G.Connected and G.IsTree ↔ GavrilSubtree.Chordal.IsChordal (totalGraph G); reason: Mathlib connectedness includes nonemptiness, tree means connected and acyclic, and the reused chordality predicate is exactly the source cycle-and-chord definition
-- source:
--   Yannakakis, Gavril, Edge dominating sets in graphs, SIAM J. Appl. Math. 38(3) (1980) 364–372, p. 370, THEOREM 5

import Mathlib
import Definitions.Def_EdgeDomSets_NPC_Supplement_TotalGraph
import Definitions.Def_GavrilSubtree_Chordal_Setting

set_option autoImplicit false

namespace EdgeDomSets.NPC.Supplement

theorem theorem_5 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) :
    G.IsTree ↔ GavrilSubtree.Chordal.IsChordal (totalGraph G) := by sorry

end EdgeDomSets.NPC.Supplement
