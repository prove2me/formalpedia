-- Prove2me | Theorems.Thm_ApproxCactus_Main_key_lemma_5_1
-- name    : ApproxCactus.Main.key_lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:02:00.753927+00:00
-- url     : https://prove2.me/theorems/a73f74c5-d668-4c6a-b948-aa31347e41a9
-- title:
--   Key Lemma 5.1 — the q-broad k-separations of a (q, k−1)-unbreakable graph are uniformly (3q+3k)-crossing
-- statement:
--   Let $G$ be a finite $(q,k-1)$-unbreakable graph and $\gamma_{5.1}(q,k):=3q+3k$. Then the set of all $q$-broad separations of $G$ of order exactly $k$ is uniformly $\gamma_{5.1}$-crossing.
--
--   Differences from the source:
--   - reading: a graph (unqualified) → a finite simple graph G : SimpleGraph V on a Fintype V with DecidableEq V; reason: the paper says "infinite graph" explicitly whenever it means one (the covering of §6); the unqualified graphs in these statements are taken to be finite
--   - encoding: a separation (A, B) of G → a pair (A, B) : Finset V × Finset V with IsSep G (A ∪ B = V(G), no edge between A ∖ B and B ∖ A); reason: the same objects; the predicate selects which pairs are separations
--   - encoding: (q, k − 1)-unbreakable: every separation of order at most k − 1 has breadth ≤ q → IsUnbreakableBelow G q k: every separation of order < k has breadth ≤ q; reason: identical for k ≥ 1; for k = 0 both are vacuous (no truncated natural subtraction k − 1)
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), Key Lemma 5.1, printed p. 41 (PDF p. 44)

import Definitions.Def_ApproxCactus_Main_Crossing

namespace ApproxCactus.Main

/-- **Key Lemma 5.1**, p. 41: if `G` is `(q, k − 1)`-unbreakable and `γ5.1(q, k) := 3q + 3k`, then
the set of all `q`-broad `k`-separations of `G` is uniformly `γ5.1`-crossing. -/
theorem key_lemma_5_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (q k : ℕ)
    (hG : IsUnbreakableBelow G q k) :
    IsUniformlyCrossing (3 * q + 3 * k)
      {s : Finset V × Finset V | IsSep G s ∧ order s = k ∧ q ≤ breadth s} := by sorry

end ApproxCactus.Main
