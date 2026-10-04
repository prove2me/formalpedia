-- Prove2me | Theorems.Thm_AppliedComb_GraphAlg_shortest_path_subpaths
-- name    : AppliedComb.GraphAlg.shortest_path_subpaths
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:36:15.669989+00:00
-- url     : https://prove2.me/theorems/e369709e-2376-4ea6-a8e3-853cb5f155cf
-- title:
--   Proposition 12.16 — subpaths of shortest paths are shortest paths
-- statement:
--   Let $G$ be a digraph with edge lengths in $\mathbb{N}_0$, let $x$ be a vertex, and let $P = (r = u_0, u_1, \dots, u_t = x)$ be a shortest path from $r$ to $x$. Then for every integer $j$ with $0 < j < t$,
--   $$(u_0, u_1, \dots, u_j) \text{ is a shortest path from } r \text{ to } u_j \quad\text{and}\quad (u_j, u_{j+1}, \dots, u_t) \text{ is a shortest path from } u_j \text{ to } u_t.$$
--
--   This optimal-substructure property of shortest paths is the first ingredient of the correctness proof of Dijkstra's algorithm (Theorem 12.18).
--
--   **Formalization Note.** The path is a list `P` with $t = |P| - 1$ and $u_j$ = `P[j]`; the prefix $(u_0, \dots, u_j)$ is `P.take (j + 1)` and the suffix $(u_j, \dots, u_t)$ is `P.drop j`. Directed paths, their lengths and shortest paths are those of the definition `AppliedComb.GraphAlg.Dijkstra` (paths have distinct vertices).
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 251, Proposition 12.16

import Mathlib
import Definitions.Def_AppliedComb_GraphAlg_Dijkstra

namespace AppliedComb.GraphAlg

/-- Keller–Trotter, p. 251, Proposition 12.16. Let `P = (r = u₀, u₁, …, u_t = x)` be a shortest
path from `r` to `x` in a digraph with edge lengths in `ℕ₀`. Then for every integer `j` with
`0 < j < t`, `(u₀, …, u_j)` is a shortest path from `r` to `u_j` and `(u_j, …, u_t)` is a
shortest path from `u_j` to `u_t`. Here `t = |P| − 1`, `u_j = P[j]`, the prefix is
`P.take (j + 1)` and the suffix is `P.drop j`. -/
theorem shortest_path_subpaths {V : Type*} (G : WeightedDigraph V) (r x : V) (P : List V)
    (hP : G.IsShortestPath r x P) (j : ℕ) (hj0 : 0 < j) (hjt : j < P.length - 1) :
    G.IsShortestPath r (P[j]'(by omega)) (P.take (j + 1)) ∧
      G.IsShortestPath (P[j]'(by omega)) x (P.drop j) := by sorry

end AppliedComb.GraphAlg
