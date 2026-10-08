-- Prove2me | Theorems.Thm_ChinesePostman_Mixed_postman_tour_exists_iff
-- name    : ChinesePostman.Mixed.postman_tour_exists_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:52:20.612093+00:00
-- url     : https://prove2.me/theorems/628f0ef0-4397-4938-a450-bb41af3286e0
-- title:
--   §7, p. 120 — a connected mixed graph has a postman tour iff no proper node set has all its boundary edges directed outward
-- statement:
--   Let $G$ be a connected mixed graph. A **postman tour** of $G$ is a tour using every edge at least once, every directed edge in its direction. Then
--
--   $$
--   G \text{ has a postman tour} \iff \text{there is no nonempty proper subset } S \subsetneq N
--   $$
--
--   such that every edge meeting one node in $S$ and one node not in $S$ is directed away from the node in $S$.
--
--   This is the existence criterion of the mixed postman problem; the condition is the obstruction to traversing an edge leaving $S$ and coming back.
--
--   **Formalization Note** "Proper subset" is read as nonempty and proper: the empty set satisfies the condition vacuously, and the whole node set has no boundary edges. Connectivity (directions ignored) is a standing assumption of the section; without it a graph with two nodes and no edges would have a one-node postman tour while $S = \{\text{one node}\}$ satisfies the condition. The node set is assumed nonempty (`[Nonempty V]`), as a graph in §2 has nodes: with no nodes there is no tour at all (a walk has at least one node), while the right-hand side holds vacuously. The paper calls necessity obvious and argues sufficiency through the algorithms of §4 and §6.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 120, §7 (existence criterion for the mixed postman problem); postman tour defined p. 119

import Mathlib
import Definitions.Def_ChinesePostman_Mixed_Setting

namespace ChinesePostman.Mixed

/-- §7, p. 120: a connected mixed graph has a postman tour if and only if there is no proper
(nonempty) subset `S` of nodes such that every edge meeting one node in `S` and one node not in
`S` is directed away from the node in `S`. -/
theorem postman_tour_exists_iff {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] [Nonempty V] (G : MixedGraph V E) (hconn : G.Connected) :
    (∃ ns es, G.IsMixedPostmanTour ns es) ↔
      ¬ ∃ S : Finset V, S.Nonempty ∧ S ≠ Finset.univ ∧
        ∀ e, (G.tail e ∈ S ↔ G.head e ∉ S) → (G.directed e = true ∧ G.tail e ∈ S) := by sorry

end ChinesePostman.Mixed
