-- Prove2me | Theorems.Thm_ApproxCactus_Main_key_lemma_11_1
-- name    : ApproxCactus.Main.key_lemma_11_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:02:27.917992+00:00
-- url     : https://prove2.me/theorems/a004fefd-39fb-4636-8c0d-1f74362d5b48
-- title:
--   Key Lemma 11.1 — the (β, k)-irrelevant separations form a star whose torso is (q, k−1)-unbreakable and (β, k)-narrow
-- statement:
--   Let $G$ be a finite $(q,k-1)$-unbreakable graph and $\beta>\beta_{11.5}(q,k)=4q+k$. Then the set $\sigma$ of all $(\beta,k)$-irrelevant separations of $G$ is a star, and the torso of $\sigma$ is $(q,k-1)$-unbreakable and $(\beta,k)$-narrow.
--
--   Differences from the source:
--   - reading: a graph (unqualified) → a finite simple graph G : SimpleGraph V on a Fintype V with DecidableEq V; reason: the paper says "infinite graph" explicitly whenever it means one (the covering of §6); the unqualified graphs in these statements are taken to be finite
--   - encoding: a separation (A, B) of G → a pair (A, B) : Finset V × Finset V with IsSep G (A ∪ B = V(G), no edge between A ∖ B and B ∖ A); reason: the same objects; the predicate selects which pairs are separations
--   - encoding: (q, k − 1)-unbreakable: every separation of order at most k − 1 has breadth ≤ q → IsUnbreakableBelow G q k: every separation of order < k has breadth ≤ q; reason: identical for k ≥ 1; for k = 0 both are vacuous (no truncated natural subtraction k − 1)
--   - encoding: the torso Z of σ, a graph on ⋂ B_i, and lifts (Definition 9.23) → torso G σ : SimpleGraph on the subtype of torsoVerts σ; IsLift G σ s ŝ with s a separation of the torso and ŝ of G, A = Â ∩ V(Z), B = B̂ ∩ V(Z), sep(s) = sep(ŝ); reason: vertices of Z are vertices of G; the subtype makes Z a graph in its own right so that separations of Z are defined by the same predicate
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), Key Lemma 11.1, printed p. 112 (PDF p. 115)

import Definitions.Def_ApproxCactus_Main_Torso

namespace ApproxCactus.Main

/-- **Key Lemma 11.1**, p. 112: if `G` is `(q, k − 1)`-unbreakable and `β > β11.5(q, k) = 4q + k`,
the set `σ` of all `(β, k)`-irrelevant separations is a star, and the torso of `σ` is
`(q, k − 1)`-unbreakable and `(β, k)`-narrow. -/
theorem key_lemma_11_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (q k β : ℕ)
    (hG : IsUnbreakableBelow G q k) (hβ : 4 * q + k < β) :
    IsStar {s : Finset V × Finset V | IsIrrelevant G β k s} ∧
      IsUnbreakableBelow (torso G {s | IsIrrelevant G β k s}) q k ∧
      IsNarrowGraph (torso G {s | IsIrrelevant G β k s}) β k := by sorry

end ApproxCactus.Main
