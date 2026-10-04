-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_shortest_augmenting_path_bound
-- name    : EdmondsKarp.ShortestPath.shortest_augmenting_path_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:16:02.875536+00:00
-- url     : https://prove2.me/theorems/665083e4-ed43-4a4b-a0e0-1daab066c320
-- title:
--   Theorem 1 (Edmonds–Karp) — fewest-arc augmentations reach a maximum flow within $\tfrac14(n^3-n)$ steps
-- statement:
--   Let $N$ be a network on $n$ nodes with source $s$, sink $t$, return arc $(t,s)$ and arbitrary positive real capacities. Run the labeling method so that each flow augmentation is done along an augmenting path having fewest arcs: $f^0$ is any flow in $N$, and for $k = 0, 1, \dots, K-1$, $P^k$ is an augmenting path with fewest arcs relative to $f^k$ and $f^{k+1}$ is obtained from $f^k$ by augmentation along $P^k$. Then
--
--   1. the number of augmentations satisfies
--   $$K \le \tfrac14 (n^3 - n);$$
--   2. if there is no augmenting path relative to $f^K$ (so that the method stops), then $f^K$ is a maximum flow.
--
--   Together, these say that a maximum flow is obtained after no more than $\tfrac14(n^3-n)$ augmentations, regardless of whether the capacities are commensurable. The bound depends on the number of nodes only; it is the analysis behind the Edmonds–Karp algorithm (breadth-first search for augmenting paths).
--
--   **Formalization Note** The bound is stated in `ℕ` as `4 * K ≤ n ^ 3 - n` with `n = Fintype.card V`; the truncated subtraction is harmless because $n \le n^3$. The run starts from an arbitrary flow, which is the setting of the paper's proof (p. 251) and contains the zero-flow start.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 251, Theorem 1

import Mathlib
import Definitions.Def_EdmondsKarp_ShortestPath_Network
import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation
import Definitions.Def_EdmondsKarp_ShortestPath_Run

namespace EdmondsKarp.ShortestPath

/-- Theorem 1 (Edmonds–Karp 1972, p. 251): if, in the labeling method for finding a maximum flow in a
network on `n` nodes, each flow augmentation is done along an augmenting path having fewest arcs, then a
maximum flow will be obtained after no more than `¼(n³ − n)` augmentations. Stated for every run
`f 0, …, f K` from an arbitrary flow `f 0`: (a) `4 K ≤ n³ − n`, and (b) if no augmenting path relative to
`f K` exists (the method stops), `f K` is a maximum flow. -/
theorem shortest_augmenting_path_bound {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsShortestRun N K f P) :
    4 * K ≤ Fintype.card V ^ 3 - Fintype.card V ∧
      ((¬ ∃ Q : List V, IsAugPath N (f K) Q) → IsMaxFlow N (f K)) := by sorry

end EdmondsKarp.ShortestPath
