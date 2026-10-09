-- Prove2me | Theorems.Thm_CycleLengthsExp_BetaGraph_theorem_4_1
-- name    : CycleLengthsExp.BetaGraph.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:24:29.34898+00:00
-- url     : https://prove2.me/theorems/b511932b-e223-49e8-a119-4ba7ddc406dd
-- title:
--   Theorem 4.1 (Haxell) — a graph with expansion d|U|+1 on small sets and d|U|+M on medium sets contains every tree on M vertices of max degree ≤ d
-- statement:
--   Let $d$, $m$ and $M$ be positive integers. Assume that $H$ is a non-empty finite graph satisfying the following two conditions:
--
--   1. for every $U\subseteq V(H)$ with $0<|U|\le m$, $\ |N_H(U)|\ge d|U|+1$;
--   2. for every $U\subseteq V(H)$ with $m<|U|\le 2m$, $\ |N_H(U)|\ge d|U|+M$.
--
--   Then $H$ contains a copy of every tree $T$ with $M$ vertices and maximum degree at most $d$:
--   $$T\subseteq H .$$
--
--   This is Haxell's generalisation (2001) of the tree-embedding theorem of Friedman and Pippenger, in the form stated by Balogh, Csaba, Pei and Samotij; the paper cites it without proof and uses it to embed the trees $T_{k,t,p}$ in the expanding subgraph of a β-graph.
--
--   **Formalization Note** "Contains a copy" means an injective map of vertices sending edges to edges (Mathlib's `SimpleGraph.IsContained`), not an induced copy. The tree $T$ lives on an arbitrary finite vertex type with $M$ elements; the host $H$ on an arbitrary non-empty finite vertex type.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 16, Theorem 4.1 (Haxell [15], as stated in [4])

import Mathlib
import Definitions.Def_CycleLengthsExp_BetaGraph_Setting

namespace CycleLengthsExp.BetaGraph

/-- Theorem 4.1 (Haxell; as stated in [4]; p. 16). Let `d, m, M` be positive integers and `H` a
non-empty finite graph such that
1. every `U` with `0 < |U| ≤ m` has `|N_H(U)| ≥ d|U| + 1`;
2. every `U` with `m < |U| ≤ 2m` has `|N_H(U)| ≥ d|U| + M`.
Then `H` contains (a copy of) every tree `T` with `M` vertices and maximum degree at most `d`. -/
theorem theorem_4_1 {W X : Type*} [Fintype W] [Nonempty W] [Fintype X]
    (H : SimpleGraph W) (d m M : ℕ) (hd : 0 < d) (hm : 0 < m) (hM : 0 < M)
    (h1 : ∀ U : Set W, 0 < U.ncard → U.ncard ≤ m → d * U.ncard + 1 ≤ (CycleLengthsExp.WellSpread.extNbhd H U).ncard)
    (h2 : ∀ U : Set W, m < U.ncard → U.ncard ≤ 2 * m → d * U.ncard + M ≤ (CycleLengthsExp.WellSpread.extNbhd H U).ncard)
    (T : SimpleGraph X) [DecidableRel T.Adj] (hT : T.IsTree) (hTcard : Fintype.card X = M)
    (hTdeg : ∀ x, T.degree x ≤ d) :
    T.IsContained H := by sorry

end CycleLengthsExp.BetaGraph
