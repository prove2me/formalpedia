-- Prove2me | Theorems.Thm_ApproxCactus_Main_lemma_11_7
-- name    : ApproxCactus.Main.lemma_11_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:01:24.099773+00:00
-- url     : https://prove2.me/theorems/98a378d6-c8e1-4be5-a286-acc410d18ea3
-- title:
--   Lemma 11.7 — for |X| < k the components of G − X with at most q vertices have at most q vertices in total
-- statement:
--   Let $G$ be a finite $(q,k-1)$-unbreakable graph with $|V(G)|\ge\nu_{11.7}(q,k):=3q+k$, and $X$ a set of fewer than $k$ vertices. Then the union of all connected components of $G-X$ with at most $q$ vertices has at most $q$ vertices.
--
--   Differences from the source:
--   - reading: a graph (unqualified) → a finite simple graph G : SimpleGraph V on a Fintype V with DecidableEq V; reason: the paper says "infinite graph" explicitly whenever it means one (the covering of §6); the unqualified graphs in these statements are taken to be finite
--   - encoding: (q, k − 1)-unbreakable: every separation of order at most k − 1 has breadth ≤ q → IsUnbreakableBelow G q k: every separation of order < k has breadth ≤ q; reason: identical for k ≥ 1; for k = 0 both are vacuous (no truncated natural subtraction k − 1)
--   - encoding: connected components of G − X and their sizes → vertex sets K of connected components of G[V ∖ X] (IsComponentOf), sizes and the size of their union as Set.ncard; reason: V is finite, so ncard is the number of vertices
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), Lemma 11.7, printed p. 113 (PDF p. 116)

import Definitions.Def_ApproxCactus_Main_Separations

namespace ApproxCactus.Main

/-- **Lemma 11.7**, p. 113: if `G` is `(q, k − 1)`-unbreakable with `|V(G)| ⩾ ν11.7(q, k) := 3q + k`
and `X` is a set of fewer than `k` vertices, then the union of all components of `G − X` with at
most `q` vertices has at most `q` vertices. -/
theorem lemma_11_7 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (q k : ℕ)
    (hG : IsUnbreakableBelow G q k) (hV : 3 * q + k ≤ Fintype.card V)
    (X : Finset V) (hX : X.card < k) :
    (⋃₀ {K : Set V | IsComponentOf G X K ∧ K.ncard ≤ q}).ncard ≤ q := by sorry

end ApproxCactus.Main
