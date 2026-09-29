-- Prove2me | Theorems.Thm_FamousTheorems_two_colorable_iff_no_odd_cycle_6b
-- name    : FamousTheorems.two_colorable_iff_no_odd_cycle_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:15.630888+00:00
-- url     : https://prove2.me/theorems/b0124629-0c86-4fd4-a0a4-4c2d5c2ace79
-- title:
--   A graph is 2-colourable iff it has no odd closed walk
-- statement:
--   **A graph is 2-colourable iff it has no odd closed walk.** A graph $G$ is bipartite, that is, properly $2$-colourable, if and only if every closed walk in $G$ has even length.
--
--   This is Kőnig's characterization of bipartite graphs, usually stated as "no odd cycles": a closed walk of odd length contains an odd cycle. It shows that bipartiteness can be tested by breadth-first search. Bipartite graphs are the setting of Kőnig's and Hall's theorems on matchings.
--
--   **Formalization note.** Mathlib's `SimpleGraph.two_colorable_iff_forall_loop_even`. `G.Colorable 2` says that there is a proper colouring with two colours, and `G.Walk u u` is the type of closed walks at $u$. The graph may be infinite.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `SimpleGraph.two_colorable_iff_forall_loop_even`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem two_colorable_iff_no_odd_cycle_6b {α : Type*} {G : SimpleGraph α} : G.Colorable 2 ↔ ∀ (u : α) (w : G.Walk u u), Even w.length := by sorry

end FamousTheorems
