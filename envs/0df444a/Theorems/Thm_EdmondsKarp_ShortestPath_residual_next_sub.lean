-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_residual_next_sub
-- name    : EdmondsKarp.ShortestPath.residual_next_sub
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:13:20.273859+00:00
-- url     : https://prove2.me/theorems/f3aaa9c0-c627-4586-a55e-5703b9c828b4
-- title:
--   Proposition 2 — new residual arcs are reversals of arcs of $P^k$
-- statement:
--   Consider a run $f^0, \dots, f^K$ of the labeling method with fewest-arc augmenting paths $P^0, \dots, P^{K-1}$, and write $N^k$ for the residual network of $f^k$. For every $k < K$ and all nodes $u, v$:
--
--   $$(u,v) \in N^{k+1} \implies (u,v) \in N^k \ \text{ or } \ (v,u) \in P^k,$$
--
--   where $(v,u) \in P^k$ means that $(v,u)$ is one of the consecutive pairs of the node sequence $P^k$.
--
--   The only arcs an augmentation can add to the residual network are the reversals of arcs of the augmenting path; this is used in Lemma 1 and Proposition 3.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 252, Proposition 2

import Mathlib
import Definitions.Def_EdmondsKarp_ShortestPath_Network
import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation
import Definitions.Def_EdmondsKarp_ShortestPath_Run

namespace EdmondsKarp.ShortestPath

/-- Proposition 2 (p. 252): if `(u, v) ∈ N^{k+1}` then `(u, v) ∈ N^k` or `(v, u) ∈ P^k`. -/
theorem residual_next_sub {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsShortestRun N K f P)
    (k : ℕ) (hk : k < K) (u v : V) (h : ResArc N (f (k + 1)) u v) :
    ResArc N (f k) u v ∨ (v, u) ∈ pathArcs (P k) := by sorry

end EdmondsKarp.ShortestPath
