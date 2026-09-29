-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_bottleneck_count_le
-- name    : EdmondsKarp.ShortestPath.bottleneck_count_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:15:29.921994+00:00
-- url     : https://prove2.me/theorems/6cfa8606-cb21-44cf-b9fa-d12d25b7d8e1
-- title:
--   Proof of Theorem 1 — each pair $\{u,v\}$ is a bottleneck at most $\tfrac12(n+1)$ times
-- statement:
--   Let $N$ be a network on $n$ nodes and consider a run $f^0, \dots, f^K$ of the labeling method with fewest-arc augmenting paths $P^0, \dots, P^{K-1}$. For every pair of nodes $u, v$, let $b(u,v)$ be the number of indices $k < K$ such that $(u,v)$ or $(v,u)$ is a bottleneck arc relative to $P^k$ and $f^k$. Then
--
--   $$b(u,v) \le \tfrac12 (n+1), \quad \text{i.e.} \quad 2\, b(u,v) \le n + 1.$$
--
--   Summing over the $\binom n2$ pairs gives the bound $\tfrac14(n^3 - n)$ of Theorem 1, since every augmentation has at least one bottleneck arc.
--
--   **Formalization Note** The count is the cardinality of a filtered `Finset.range K`; the bound is stated multiplied by $2$ to stay in `ℕ`.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 252, proof of Theorem 1 (unnumbered: "the number of occurrences of (u, v) or (v, u) as a bottleneck arc throughout the entire labeling method is at most ½(n + 1)")

import Mathlib
import Definitions.Def_EdmondsKarp_ShortestPath_Network
import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation
import Definitions.Def_EdmondsKarp_ShortestPath_Run

namespace EdmondsKarp.ShortestPath

open Classical in
/-- Proof of Theorem 1 (p. 252): for every pair of nodes `u, v`, the number of occurrences of `(u, v)`
or `(v, u)` as a bottleneck arc throughout the first `K` augmentations is at most `½(n + 1)`,
where `n` is the number of nodes. -/
theorem bottleneck_count_le {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsShortestRun N K f P) (u v : V) :
    2 * ((Finset.range K).filter (fun k =>
        IsBottleneck N (f k) (P k) u v ∨ IsBottleneck N (f k) (P k) v u)).card
      ≤ Fintype.card V + 1 := by sorry

end EdmondsKarp.ShortestPath
