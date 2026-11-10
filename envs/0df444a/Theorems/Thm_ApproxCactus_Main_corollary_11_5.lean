-- Prove2me | Theorems.Thm_ApproxCactus_Main_corollary_11_5
-- name    : ApproxCactus.Main.corollary_11_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:02:03.473979+00:00
-- url     : https://prove2.me/theorems/3d448667-2515-41e9-99ed-99f9521b728e
-- title:
--   Corollary 11.5 — for β > 4q + k the small side of an irrelevant separation misses the separator of every β-broad k-separation
-- statement:
--   Let $G$ be a finite $(q,k-1)$-unbreakable graph and $\beta>\beta_{11.5}(q,k):=4q+k$. Let $s'=(A',B')$ be a $(\beta,k)$-irrelevant separation and $t$ a $\beta$-broad separation of $G$ of order exactly $k$. Then $A'\setminus B'$ is disjoint from $\mathrm{sep}(t)$.
--
--   Differences from the source:
--   - reading: a graph (unqualified) → a finite simple graph G : SimpleGraph V on a Fintype V with DecidableEq V; reason: the paper says "infinite graph" explicitly whenever it means one (the covering of §6); the unqualified graphs in these statements are taken to be finite
--   - encoding: a separation (A, B) of G → a pair (A, B) : Finset V × Finset V with IsSep G (A ∪ B = V(G), no edge between A ∖ B and B ∖ A); reason: the same objects; the predicate selects which pairs are separations
--   - encoding: (q, k − 1)-unbreakable: every separation of order at most k − 1 has breadth ≤ q → IsUnbreakableBelow G q k: every separation of order < k has breadth ≤ q; reason: identical for k ≥ 1; for k = 0 both are vacuous (no truncated natural subtraction k − 1)
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), Corollary 11.5, printed p. 113 (PDF p. 116)

import Definitions.Def_ApproxCactus_Main_Torso

namespace ApproxCactus.Main

/-- **Corollary 11.5**, p. 113: if `G` is `(q, k − 1)`-unbreakable, `β > β11.5(q, k) := 4q + k`,
`s' = (A', B')` is `(β, k)`-irrelevant and `t` is a `β`-broad `k`-separation of `G`, then `A' ∖ B'`
is disjoint from `sep(t)`. -/
theorem corollary_11_5 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (q k β : ℕ)
    (hG : IsUnbreakableBelow G q k) (hβ : 4 * q + k < β) (s' t : Finset V × Finset V)
    (hs' : IsIrrelevant G β k s') (ht : IsSep G t) (htk : order t = k) (htb : β ≤ breadth t) :
    Disjoint (s'.1 \ s'.2) (sep t) := by sorry

end ApproxCactus.Main
