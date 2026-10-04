-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_critical_edge_count_le
-- name    : EdmondsKarp.ShortestPath.critical_edge_count_le
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-30T22:36:37.662682+00:00
-- url     : https://prove2.me/theorems/d27ff656-c127-4694-9f05-38ac81139ddd
-- title:
--   Critical-edge count lemma: each arc is critical in at most (card V - 1)/2 shortest-augmenting-path augmentations
-- statement:
--   Edmonds-Karp (1972), p. 251, critical-edge counting lemma: the elementary input to Theorem 1 (EdmondsKarp.ShortestPath.shortest_augmenting_path_bound). In a shortest-augmenting-path run, let d(k,v) be the residual distance label of node v after k augmentations (the fewest-arc distance from the source in the residual graph). The paper's proof shows these labels are nondecreasing in k, and that whenever an arc (u,v) is critical in augmentation k -- i.e. it is the bottleneck arc saturated by that augmentation -- the label at u jumps by at least 2. Since every label is below n = card V, each arc is critical in at most (n-1)/2 augmentations: m critical uses force 2*m < n. This is the counting step that, combined with the bound on the number of arcs, yields the n^3/4 augmentation bound of Theorem 1. Stated abstractly over the distance labels d and the critical-step finsets C (to be instantiated from IsShortestRun by the proof worker); the counting core is pure Fintype/Finset nat arithmetic.

import Mathlib
import Definitions.Def_EdmondsKarp_ShortestPath_Network
import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation
import Definitions.Def_EdmondsKarp_ShortestPath_Run

namespace EdmondsKarp.ShortestPath

/-- Edmonds-Karp (1972), p. 251, critical-edge counting lemma: input to
    Theorem 1 (`shortest_augmenting_path_bound`). In a shortest-augmenting-path
    run `hrun : IsShortestRun N K f P`, write `d k v` for the residual distance
    label of `v` after `k` augmentations (fewest arcs from the source) and
    `C u v` for the finite set of augmentations in which the arc `(u, v)` is
    critical. The labels are nondecreasing (`hmono`) and grow by at least two
    at `u` whenever `(u, v)` is critical (`hcrit`); every label is below
    `n = Fintype.card V` (`hbound`). Hence each arc is critical in at most
    `(n - 1) / 2` augmentations: after `m` critical uses the label at `u` has
    grown by `2 * m`, so `2 * m < n`. This is the elementary counting step
    behind the `n ^ 3 / 4` augmentation bound of Theorem 1. -/
theorem critical_edge_count_le {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V)
    (hrun : IsShortestRun N K f P)
    (d : ℕ → V → ℕ) (C : V → V → Finset ℕ)
    (hmono : ∀ k v, d k v ≤ d (k + 1) v)
    (hcrit : ∀ u v k, k ∈ C u v → d (k + 1) u ≥ d k u + 2)
    (hbound : ∀ k v, d k v < Fintype.card V) :
    ∀ u v, (C u v).card ≤ (Fintype.card V - 1) / 2 := by
  sorry

end EdmondsKarp.ShortestPath
