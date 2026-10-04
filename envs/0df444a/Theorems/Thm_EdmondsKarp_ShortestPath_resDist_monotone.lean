-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_resDist_monotone
-- name    : EdmondsKarp.ShortestPath.resDist_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:14:24.794123+00:00
-- url     : https://prove2.me/theorems/8d9dee16-f285-439b-8312-c0732709db6b
-- title:
--   Proposition 3 — residual distances from $s$ and to $t$ never decrease
-- statement:
--   Consider a run $f^0, \dots, f^K$ of the labeling method in a network $N$ with source $s$ and sink $t$, in which each augmentation is along an augmenting path having fewest arcs. Let $\delta^k(u,v) \in \{0,1,2,\dots\} \cup \{\infty\}$ be the distance from $u$ to $v$ in the residual network $N^k$ of $f^k$. For every $k < K$ and every node $u$,
--
--   $$\delta^k(s,u) \le \delta^{k+1}(s,u) \qquad (1)$$
--
--   and
--
--   $$\delta^k(u,t) \le \delta^{k+1}(u,t). \qquad (2)$$
--
--   This monotonicity of distances under shortest-path augmentation is the key ingredient of Lemma 2.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 252, Proposition 3, (1) and (2)

import Mathlib
import Definitions.Def_EdmondsKarp_ShortestPath_Network
import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation
import Definitions.Def_EdmondsKarp_ShortestPath_Run

namespace EdmondsKarp.ShortestPath

/-- Proposition 3 (p. 252): for `k = 0, 1, 2, …` and all `u`, `δ^k(s, u) ≤ δ^{k+1}(s, u)` (1) and
`δ^k(u, t) ≤ δ^{k+1}(u, t)` (2). -/
theorem resDist_monotone {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsShortestRun N K f P)
    (k : ℕ) (hk : k < K) (u : V) :
    resDist N (f k) N.s u ≤ resDist N (f (k + 1)) N.s u ∧
      resDist N (f k) u N.t ≤ resDist N (f (k + 1)) u N.t := by sorry

end EdmondsKarp.ShortestPath
