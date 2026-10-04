-- Prove2me | Theorems.Thm_AppliedComb_GraphAlg_dijkstra_correct
-- name    : AppliedComb.GraphAlg.dijkstra_correct
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:37:15.96981+00:00
-- url     : https://prove2.me/theorems/9f648ac6-3d59-4b3f-82cb-a8eda3d58f29
-- title:
--   Theorem 12.18 — Dijkstra's algorithm yields shortest paths
-- statement:
--   Let $G = (V, E)$ be a finite digraph with edge lengths $w : E \to \mathbb{N}_0$ and let $r \in V$ be a root. Run Dijkstra's algorithm (Algorithm 12.14) from $r$, with any admissible choices among ties, until it terminates at Step $n = |V|$. Then for every vertex $x \in V$,
--   $$\delta(x) = \operatorname{dist}(r, x),$$
--   and, whenever $\operatorname{dist}(r, x) < \infty$, the sequence $P(x)$ is a shortest path from $r$ to $x$.
--
--   This is the correctness theorem for the single-source shortest path problem with non-negative lengths (Problem 12.13): the algorithm computes all distances from $r$ together with a shortest path to every vertex.
--
--   **Formalization Note.** The algorithm, its tie-breaking and its halting state are the definition `AppliedComb.GraphAlg.Dijkstra`; the theorem quantifies over every halted state `s` (`DijkstraRun G r (Fintype.card V) s`), so it covers every run. Distances and $\delta$ take values in `ℕ∞`. The book's theorem speaks of "the distance from $r$ to $x$" and "a shortest path" without addressing vertices unreachable from $r$; for those the distance is the minimum over the empty set, read as $\infty$, and the first conclusion asserts $\delta(x) = \infty$, while the second conclusion is asserted only for vertices at finite distance (an unreachable vertex has no path at all).
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 251, Theorem 12.18 (Algorithm 12.14, pp. 246–247)

import Mathlib
import Definitions.Def_AppliedComb_GraphAlg_Dijkstra

namespace AppliedComb.GraphAlg

/-- Keller–Trotter, p. 251, Theorem 12.18. Dijkstra's algorithm yields shortest paths for every
vertex: when Dijkstra's algorithm (Algorithm 12.14) with root `r` terminates, at Step `n = |V|`,
for each `x ∈ V` the value `δ(x)` is the distance from `r` to `x` and `P(x)` is a shortest path
from `r` to `x`. This holds for every run (every admissible tie-breaking). When no directed path
from `r` to `x` exists the distance is `∞` and the first conclusion says `δ(x) = ∞`; the second
conclusion is asserted for the vertices at finite distance, the only ones having a path. -/
theorem dijkstra_correct {V : Type*} [Fintype V] (G : WeightedDigraph V) (r : V)
    (s : DijkstraState V) (hs : DijkstraRun G r (Fintype.card V) s) :
    ∀ x : V, s.δ x = G.dist r x ∧ (G.dist r x ≠ ⊤ → G.IsShortestPath r x (s.P x)) := by sorry

end AppliedComb.GraphAlg
