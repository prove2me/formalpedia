-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_resDist_add_two_of_reversed
-- name    : EdmondsKarp.ShortestPath.resDist_add_two_of_reversed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:14:56.536184+00:00
-- url     : https://prove2.me/theorems/eb1fa8eb-0cd9-44a8-b90f-009f74ee53e8
-- title:
--   Lemma 2 — using $(u,v)$ and later $(v,u)$ raises $\delta(s,t)$ by at least 2
-- statement:
--   Consider a run $f^0, \dots, f^K$ of the labeling method with fewest-arc augmenting paths $P^0, \dots, P^{K-1}$, and let $\delta^k(s,t)$ be the distance from $s$ to $t$ in the residual network of $f^k$. If $k < l < K$, $(u,v) \in P^k$ and $(v,u) \in P^l$, then
--
--   $$\delta^l(s,t) \ge \delta^k(s,t) + 2.$$
--
--   Since $\delta(s,t)$ never exceeds $n-1$ while finite, this lemma limits how often a pair of nodes can alternate in augmenting paths.
--
--   **Formalization Note** The inequality is in `ℕ∞`, with $\infty + 2 = \infty$.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 251, Lemma 2

import Mathlib
import Definitions.Def_EdmondsKarp_ShortestPath_Network
import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation
import Definitions.Def_EdmondsKarp_ShortestPath_Run

namespace EdmondsKarp.ShortestPath

/-- Lemma 2 (p. 251): if `k < l`, `(u, v) ∈ P^k` and `(v, u) ∈ P^l`, then
`δ^l(s, t) ≥ δ^k(s, t) + 2`. -/
theorem resDist_add_two_of_reversed {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsShortestRun N K f P)
    (k l : ℕ) (hkl : k < l) (hl : l < K) (u v : V)
    (huv : (u, v) ∈ pathArcs (P k)) (hvu : (v, u) ∈ pathArcs (P l)) :
    resDist N (f k) N.s N.t + 2 ≤ resDist N (f l) N.s N.t := by sorry

end EdmondsKarp.ShortestPath
