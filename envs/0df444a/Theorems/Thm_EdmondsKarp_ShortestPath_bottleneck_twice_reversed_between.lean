-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_bottleneck_twice_reversed_between
-- name    : EdmondsKarp.ShortestPath.bottleneck_twice_reversed_between
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:13:52.145726+00:00
-- url     : https://prove2.me/theorems/42a7c5c4-cdda-4a43-8993-cd580fc5ebfa
-- title:
--   Lemma 1 — between two bottleneck occurrences of $(u,v)$ the reversed arc $(v,u)$ is used
-- statement:
--   Consider a run $f^0, \dots, f^K$ of the labeling method with fewest-arc augmenting paths $P^0, \dots, P^{K-1}$. Let $k < m < K$ and suppose $(u,v)$ is a bottleneck arc relative to $P^k$ and $f^k$, and also relative to $P^m$ and $f^m$. Then
--
--   $$\exists\, l \text{ with } k < l < m \text{ such that } (v,u) \in P^l.$$
--
--   Combined with Lemma 2, this bounds how often a given pair of nodes can supply a bottleneck arc.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 251, Lemma 1

import Mathlib
import Definitions.Def_EdmondsKarp_ShortestPath_Network
import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation
import Definitions.Def_EdmondsKarp_ShortestPath_Run

namespace EdmondsKarp.ShortestPath

/-- Lemma 1 (p. 251): if `k < m` and `(u, v)` is a bottleneck arc relative to `P^k` and `f^k`, and also
relative to `P^m` and `f^m`, then, for some `l` such that `k < l < m`, `(v, u) ∈ P^l`. -/
theorem bottleneck_twice_reversed_between {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsShortestRun N K f P)
    (k m : ℕ) (hkm : k < m) (hmK : m < K) (u v : V)
    (hbk : IsBottleneck N (f k) (P k) u v) (hbm : IsBottleneck N (f m) (P m) u v) :
    ∃ l, k < l ∧ l < m ∧ (v, u) ∈ pathArcs (P l) := by sorry

end EdmondsKarp.ShortestPath
