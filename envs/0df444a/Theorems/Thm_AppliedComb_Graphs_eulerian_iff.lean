-- Prove2me | Theorems.Thm_AppliedComb_Graphs_eulerian_iff
-- name    : AppliedComb.Graphs.eulerian_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:01:47.364925+00:00
-- url     : https://prove2.me/theorems/ff6b9d2c-810a-4a77-92bb-3b905412b933
-- title:
--   Theorem 5.13 — Euler: a graph is eulerian iff it is connected and all degrees are even
-- statement:
--   Let $G = (V, E)$ be a finite graph without isolated vertices (every vertex has at least one neighbour). Then $G$ is eulerian (it has a closed sequence of vertices that traverses every edge exactly once) if and only if
--   $$G \text{ is connected} \quad\text{and}\quad \deg_G(v) \text{ is even for every } v \in V.$$
--
--   This is Euler's 1736 characterization, the result with which the book opens the theory of graph traversals.
--
--   **Formalization Note.** The book defines "eulerian" only for graphs without isolated vertices (p. 75), so that restriction is a hypothesis here; without it the equivalence fails, e.g. an edgeless graph on two vertices has an eulerian circuit in the sense of the definition (a one-vertex sequence covers its empty edge set) but is disconnected. Connectedness is Mathlib's `SimpleGraph.Connected`, which includes nonemptiness of $V$.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 77, Theorem 5.13 (definition of eulerian on p. 75)

import Mathlib
import Definitions.Def_AppliedComb_Graphs_IsEulerian

namespace AppliedComb.Graphs

/-- Keller–Trotter, p. 77, Theorem 5.13 (Euler). For a finite graph `G` without isolated
vertices (the class on which the book defines "eulerian", p. 75), `G` is eulerian if and only
if it is connected and every vertex has even degree. -/
theorem eulerian_iff {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ v : V, ∃ w : V, G.Adj v w) :
    IsEulerian G ↔ G.Connected ∧ ∀ v : V, Even (G.degree v) := by sorry

end AppliedComb.Graphs
