-- Prove2me | Theorems.Thm_ApproxCactus_Main_key_lemma_4_14
-- name    : ApproxCactus.Main.key_lemma_4_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:01:56.627204+00:00
-- url     : https://prove2.me/theorems/4d64644c-dfb5-4e1a-a45b-de050327d01d
-- title:
--   Key Lemma 4.14 (3D Corner Lemma) — an equitable (2q+k)-criss-compatible triple of k-separations is uniformly crossing
-- statement:
--   Let $G$ be a finite $(q,k-1)$-unbreakable graph and $r,s,t$ separations of $G$ of order exactly $k$ such that $S=\{r,s,t\}$ is equitable and $(2q+k)$-criss-compatible. Then $S$ is uniformly crossing (uniformly $0$-crossing).
--
--   Differences from the source:
--   - reading: a graph (unqualified) → a finite simple graph G : SimpleGraph V on a Fintype V with DecidableEq V; reason: the paper says "infinite graph" explicitly whenever it means one (the covering of §6); the unqualified graphs in these statements are taken to be finite
--   - encoding: a separation (A, B) of G → a pair (A, B) : Finset V × Finset V with IsSep G (A ∪ B = V(G), no edge between A ∖ B and B ∖ A); reason: the same objects; the predicate selects which pairs are separations
--   - encoding: (q, k − 1)-unbreakable: every separation of order at most k − 1 has breadth ≤ q → IsUnbreakableBelow G q k: every separation of order < k has breadth ≤ q; reason: identical for k ≥ 1; for k = 0 both are vacuous (no truncated natural subtraction k − 1)
--   - generalization: an equitable (2q + k)-criss-compatible triple of k-separations → any three k-separations r, s, t, not necessarily distinct, with S = {r, s, t}; reason: three distinct separations are the special case; the statement is the source's for every triple
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), Key Lemma 4.14, printed p. 38 (PDF p. 41)

import Definitions.Def_ApproxCactus_Main_Crossing

namespace ApproxCactus.Main

/-- **Key Lemma 4.14 (3D Corner Lemma)**, p. 38: if `G` is `(q, k − 1)`-unbreakable and
`S = {r, s, t}` is an equitable `(2q + k)`-criss-compatible triple of `k`-separations of `G`, then
`S` is uniformly crossing (uniformly `0`-crossing). -/
theorem key_lemma_4_14 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (q k : ℕ)
    (hG : IsUnbreakableBelow G q k) (r s t : Finset V × Finset V)
    (hr : IsSep G r) (hs : IsSep G s) (ht : IsSep G t)
    (hrk : order r = k) (hsk : order s = k) (htk : order t = k)
    (heq : IsEquitable k {r, s, t}) (hcriss : IsCrissCompatible (2 * q + k) {r, s, t}) :
    IsUniformlyCrossing 0 {r, s, t} := by sorry

end ApproxCactus.Main
