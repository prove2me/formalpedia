-- Prove2me | Theorems.Thm_ApproxCactus_Main_theorem_1_2
-- name    : ApproxCactus.Main.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:02:27.29837+00:00
-- url     : https://prove2.me/theorems/7a774a8c-bbed-46dd-90a7-36733370f4b0
-- title:
--   Theorem 1.2 (Main theorem) — (q, k−1)-unbreakable graphs have cactus-decompositions displaying (⩽k)-separations within edit-distance d(q, k) of every (⩽k)-separation
-- statement:
--   For all $q,k\in\mathbb N$ there is $d\in\mathbb N$ such that every finite $(q,k-1)$-unbreakable graph $G$ (every separation of order $<k$ has breadth $\le q$) has a cactus-decomposition $\mathcal C$ such that every separation displayed by $\mathcal C$ has order $\le k$, and every separation $(A,B)$ of $G$ of order $\le k$ has edit-distance at most $d$ to some displayed separation $(C,D)$, i.e. $|A\triangle C|\le d$ and $|B\triangle D|\le d$. The bound $d$ depends only on $q$ and $k$.
--
--   Differences from the source:
--   - reading: a graph (unqualified) → a finite simple graph G : SimpleGraph V on a Fintype V with DecidableEq V; reason: the paper says "infinite graph" explicitly whenever it means one (the covering of §6); the unqualified graphs in these statements are taken to be finite
--   - encoding: a separation (A, B) of G → a pair (A, B) : Finset V × Finset V with IsSep G (A ∪ B = V(G), no edge between A ∖ B and B ∖ A); reason: the same objects; the predicate selects which pairs are separations
--   - encoding: (q, k − 1)-unbreakable: every separation of order at most k − 1 has breadth ≤ q → IsUnbreakableBelow G q k: every separation of order < k has breadth ≤ q; reason: identical for k ≥ 1; for k = 0 both are vacuous (no truncated natural subtraction k − 1)
--   - encoding: graph-decomposition (H, V) with H a strong cactus, a cycle Z_ℓ or a star, and designated P-nodes → Decomp G: a finite loopless multigraph (node type, edge type, endpoint map), bags as Finsets, a set of P-nodes, (H1) and (H2); reason: cacti, cycles and stars are loopless; parallel edges are kept so that Z_2 is a 2-cycle; any finite multigraph can be relabelled by types in Type
--   - reading: "admits a cactus-decomposition displaying (⩽k)-separations" → every separation displayed by the cactus-decomposition has order ≤ k; reason: the proof on p. 117 establishes exactly this ("every displayed separation has order ⩽ k"), as does Theorem 10.7
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), Theorem 1.2, printed p. 3 (PDF p. 6)

import Definitions.Def_ApproxCactus_Main_Decompositions

namespace ApproxCactus.Main

/-- **Theorem 1.2 (Main theorem)**, p. 3: for all `q, k ∈ ℕ` there is `d ∈ ℕ` such that every
`(q, k − 1)`-unbreakable finite graph `G` admits a cactus-decomposition displaying
`(⩽ k)`-separations (every displayed separation has order `⩽ k`) such that every
`(⩽ k)`-separation of `G` has edit-distance at most `d` to a displayed separation. -/
theorem theorem_1_2 (q k : ℕ) :
    ∃ d : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsUnbreakableBelow G q k →
      ∃ C : Decomp G, C.IsStrongCactus ∧ (∀ s, C.IsDisplayed s → order s ≤ k) ∧
        ∀ s : Finset V × Finset V, IsSep G s → order s ≤ k →
          ∃ t, C.IsDisplayed t ∧ EditDistLe d s t := by sorry

end ApproxCactus.Main
