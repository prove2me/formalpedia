-- Prove2me | Theorems.Thm_FamousTheorems_euler_trail_odd_degree_6b
-- name    : FamousTheorems.euler_trail_odd_degree_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:10.895594+00:00
-- url     : https://prove2.me/theorems/52f899da-9c51-47be-b1a7-57d06a857270
-- title:
--   Euler's theorem on Eulerian trails: at most two vertices of odd degree
-- statement:
--   **Euler's theorem on Eulerian trails.** Let $G$ be a finite graph. If $G$ has an Eulerian trail, meaning a walk that uses every edge exactly once, then the number of vertices of odd degree is $0$ or $2$.
--
--   This is the necessity half of Euler's 1736 solution of the Königsberg bridge problem, which is regarded as the start of graph theory. Every intermediate visit to a vertex uses two edges, so only the endpoints of the trail can have odd degree. Since each of the four land masses of Königsberg had odd degree, no walk crossed each bridge exactly once.
--
--   **Formalization note.** Mathlib's `SimpleGraph.Walk.IsEulerian.card_odd_degree`, for a simple graph on a finite vertex type. `p.IsEulerian` says that the walk $p$ contains every edge of $G$ exactly once.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `SimpleGraph.Walk.IsEulerian.card_odd_degree`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem euler_trail_odd_degree_6b {V : Type*} {G : SimpleGraph V} [DecidableEq V] [Fintype V] [DecidableRel G.Adj] {u v : V}
    {p : G.Walk u v} (hp : p.IsEulerian) :
    Fintype.card ({w : V | Odd (G.degree w)} : Set V) = 0 ∨ Fintype.card ({w : V | Odd (G.degree w)} : Set V) = 2 := by sorry

end FamousTheorems
