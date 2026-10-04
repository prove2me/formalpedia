-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_bottleneck_not_residual_next
-- name    : EdmondsKarp.ShortestPath.bottleneck_not_residual_next
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:12:24.412077+00:00
-- url     : https://prove2.me/theorems/608f92be-47ba-4d93-883c-1363b2ee16a9
-- title:
--   Proposition 1 — a bottleneck arc of $P^k$ is not an arc of $N^{k+1}$
-- statement:
--   Consider a run $f^0, f^1, \dots, f^K$ of the labeling method in a network $N$ in which $f^0$ is a flow and each $f^{k+1}$ is obtained from $f^k$ by augmentation along an augmenting path $P^k$ having fewest arcs. Write $N^k$ for the residual network of $f^k$. For every $k < K$ and every pair of nodes $(u,v)$:
--
--   $$(u,v) \text{ is a bottleneck arc relative to } P^k \text{ and } f^k \implies (u,v) \notin N^{k+1}.$$
--
--   This proposition, together with Proposition 2, drives Lemma 1: a bottleneck arc disappears from the residual network and can only come back after it has been traversed in the opposite direction.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 252, Proposition 1

import Mathlib
import Definitions.Def_EdmondsKarp_ShortestPath_Network
import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation
import Definitions.Def_EdmondsKarp_ShortestPath_Run

namespace EdmondsKarp.ShortestPath

/-- Proposition 1 (p. 252): if `(u, v)` is a bottleneck arc relative to `P^k` and `f^k`, then
`(u, v) ∉ N^{k+1}`. -/
theorem bottleneck_not_residual_next {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsShortestRun N K f P)
    (k : ℕ) (hk : k < K) (u v : V) (hb : IsBottleneck N (f k) (P k) u v) :
    ¬ ResArc N (f (k + 1)) u v := by sorry

end EdmondsKarp.ShortestPath
