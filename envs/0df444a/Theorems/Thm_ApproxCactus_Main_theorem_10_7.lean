-- Prove2me | Theorems.Thm_ApproxCactus_Main_theorem_10_7
-- name    : ApproxCactus.Main.theorem_10_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:02:12.140624+00:00
-- url     : https://prove2.me/theorems/da22b332-78f2-4d2c-bf1f-b5f30b215a36
-- title:
--   Theorem 10.7 — (q, k−1)-unbreakable (b, k)-narrow graphs have clique-faithful cactus-decompositions η-approximating their k-separations
-- statement:
--   For all $q,k,b\in\mathbb N$ there is $\eta=\eta_{10.7}(q,k,b)\in\mathbb N$ such that every finite $(q,k-1)$-unbreakable $(b,k)$-narrow graph $G$ has a clique-faithful cactus-decomposition $\mathcal C$ such that every displayed separation has order $\le k$ and the set of displayed separations of $\mathcal C$ $\eta$-approximates the set of all separations of $G$ of order exactly $k$.
--
--   Differences from the source:
--   - reading: a graph (unqualified) → a finite simple graph G : SimpleGraph V on a Fintype V with DecidableEq V; reason: the paper says "infinite graph" explicitly whenever it means one (the covering of §6); the unqualified graphs in these statements are taken to be finite
--   - encoding: a separation (A, B) of G → a pair (A, B) : Finset V × Finset V with IsSep G (A ∪ B = V(G), no edge between A ∖ B and B ∖ A); reason: the same objects; the predicate selects which pairs are separations
--   - encoding: (q, k − 1)-unbreakable: every separation of order at most k − 1 has breadth ≤ q → IsUnbreakableBelow G q k: every separation of order < k has breadth ≤ q; reason: identical for k ≥ 1; for k = 0 both are vacuous (no truncated natural subtraction k − 1)
--   - encoding: graph-decomposition (H, V) with H a strong cactus, a cycle Z_ℓ or a star, and designated P-nodes → Decomp G: a finite loopless multigraph (node type, edge type, endpoint map), bags as Finsets, a set of P-nodes, (H1) and (H2); reason: cacti, cycles and stars are loopless; parallel edges are kept so that Z_2 is a 2-cycle; any finite multigraph can be relabelled by types in Type
--   - reading: clique of G → any Finset K with G.IsClique K, including ∅ and singletons; reason: the source does not exclude them; including them is the stronger reading of the conclusion
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), Theorem 10.7, printed p. 107 (PDF p. 110)

import Definitions.Def_ApproxCactus_Main_Decompositions

namespace ApproxCactus.Main

/-- **Theorem 10.7**, p. 107: for all `q, k, b` there is `η = η10.7(q, k, b)` such that every
`(q, k − 1)`-unbreakable `(b, k)`-narrow graph `G` has a clique-faithful cactus-decomposition `C`
all of whose displayed separations have order `⩽ k` and whose displayed separations
`η`-approximate the set of all `k`-separations of `G`. -/
theorem theorem_10_7 (q k b : ℕ) :
    ∃ η : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsUnbreakableBelow G q k → IsNarrowGraph G b k →
      ∃ C : Decomp G, C.IsStrongCactus ∧ C.IsCliqueFaithful ∧
        (∀ s, C.IsDisplayed s → order s ≤ k) ∧
        Approximates η {s | C.IsDisplayed s} {s | IsSep G s ∧ order s = k} := by sorry

end ApproxCactus.Main
