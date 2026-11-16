-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_Supplement_lemma_39
-- name    : DistancePreserver934.Exact.Supplement.lemma_39
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:29:09.532204+00:00
-- url     : https://prove2.me/theorems/a6aac47e-9423-4110-a7b8-9d4aed01aae7
-- title:
--   Lemma 39 — A source-independent clustering reduction that preserves every reachable source pair
-- statement:
--   For every integer $\Delta\ge1$ and $n$-vertex graph $G$, there are a single subgraph $J_0\subseteq G$ and vertex set $R$ satisfying
--
--   $$|E(J_0)|\le2n\Delta,\qquad |R|\le n/\Delta,$$
--
--   such that, for every source set $S$, integer $\beta\ge0$ and auxiliary additive $+\beta$ spanner on the reachable pairs in $S\times R$, its union with $J_0$ is a complete sourcewise additive $+(\beta+2)$ spanner. The same $J_0,R$ work for all sources and auxiliary spanners. Empty sets are allowed; no uniqueness or membership restriction is placed on cluster centers. The coefficient 2 follows from the proof's $n+n\Delta$ cost. This is the source-independent reduction for Theorem 40.
--
--   Differences from the source:
--   - encoding: finite graphs on n vertices, with the section demand convention → an arbitrary finite vertex type, unordered technical demands in §4 and §7.1–7.2 and ordered demands in Definition 26 and §8; reason: the published graph and extended-distance definitions retain exactly these instances; undirected edges are counted once
--   - encoding: O(nΔ) clustering cost → at most 2nΔ edges; reason: the proof retains at most n star edges and fewer than nΔ further edges, and Δ≥1
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026); canonical source.pdf SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b; Lemma 39, printed p. 34 (PDF p. 35)

import Definitions.Def_DistancePreserver934_Exact_Supplement_EdgePaths
import Definitions.Def_DistancePreserver934_Exact_Supplement_Hitting
import Definitions.Def_DistancePreserver934_Exact_Supplement_Sourcewise
import Definitions.Def_DistancePreserver934_Exact_Supplement_Budgets

set_option autoImplicit false

namespace DistancePreserver934.Exact.Supplement

open Classical

theorem lemma_39 :

  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (Δ : ℕ), 1 ≤ Δ →
    ∃ (J0 : SimpleGraph V) (R : Finset V),
      J0 ≤ G ∧ (numEdges J0 : ℝ) ≤ 2 * (Fintype.card V : ℝ) * (Δ : ℝ) ∧
      (R.card : ℝ) ≤ (Fintype.card V : ℝ) / (Δ : ℝ) ∧
      ∀ (S : Finset V) (β : ℕ) (Jaux : SimpleGraph V),
        IsAdditive G Jaux (reachablePairs G S R) β →
        IsCompleteSourcewise G (J0 ⊔ Jaux) S (β + 2)
 := by sorry

end DistancePreserver934.Exact.Supplement
