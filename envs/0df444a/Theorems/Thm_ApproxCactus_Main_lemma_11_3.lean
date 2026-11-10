-- Prove2me | Theorems.Thm_ApproxCactus_Main_lemma_11_3
-- name    : ApproxCactus.Main.lemma_11_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:02:18.252739+00:00
-- url     : https://prove2.me/theorems/41f6f498-2943-4c9c-8afc-6e85464e00f3
-- title:
--   Lemma 11.3 — the small side of a (β, k)-irrelevant separation has at most q vertices
-- statement:
--   Let $G$ be a finite $(q,k-1)$-unbreakable graph, $\beta>q$, and $(C,D)$ a $(\beta,k)$-irrelevant separation of $G$. Then $|C\setminus D|\le q$.
--
--   Differences from the source:
--   - reading: a graph (unqualified) → a finite simple graph G : SimpleGraph V on a Fintype V with DecidableEq V; reason: the paper says "infinite graph" explicitly whenever it means one (the covering of §6); the unqualified graphs in these statements are taken to be finite
--   - encoding: a separation (A, B) of G → a pair (A, B) : Finset V × Finset V with IsSep G (A ∪ B = V(G), no edge between A ∖ B and B ∖ A); reason: the same objects; the predicate selects which pairs are separations
--   - encoding: (q, k − 1)-unbreakable: every separation of order at most k − 1 has breadth ≤ q → IsUnbreakableBelow G q k: every separation of order < k has breadth ≤ q; reason: identical for k ≥ 1; for k = 0 both are vacuous (no truncated natural subtraction k − 1)
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), Lemma 11.3, printed p. 112 (PDF p. 115)

import Definitions.Def_ApproxCactus_Main_Torso

namespace ApproxCactus.Main

/-- **Lemma 11.3**, p. 112: if `G` is `(q, k − 1)`-unbreakable, `β > q` and `(C, D)` is
`(β, k)`-irrelevant, then `|C ∖ D| ⩽ q`. -/
theorem lemma_11_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (q k β : ℕ)
    (hG : IsUnbreakableBelow G q k) (hβ : q < β) (s : Finset V × Finset V)
    (hs : IsIrrelevant G β k s) :
    (s.1 \ s.2).card ≤ q := by sorry

end ApproxCactus.Main
