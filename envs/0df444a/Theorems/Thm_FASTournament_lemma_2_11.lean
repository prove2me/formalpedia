-- Prove2me | Theorems.Thm_FASTournament_lemma_2_11
-- name    : FASTournament.lemma_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:32:54.821981+00:00
-- url     : https://prove2.me/theorems/6d5de9b6-e3a7-4eed-9119-d9a5398080df
-- title:
--   Lemma 2.11 — every tournament in $\mathcal Q$ is Möbius-free
-- statement:
--   Every tournament in the class $\mathcal Q$ is Möbius-free.
--
--   Here $\mathcal Q$ consists of the tournaments whose vertices split into a center $v$ and sets $U_1,\dots,U_k$, each a singleton or a triangle, with all arcs between $U_i$ and $U_j$ directed to $U_j$ for $i<j$. The vertical blocks of the structure $\mathcal P$ are in $\mathcal Q$.
--
--   Differences from the source:
--   - encoding: a tournament T = (V, A) (finite) → T : Digraph V on a Fintype V with IsTournament T (no loops; exactly one of u → v, v → u for u ≠ v); reason: the same objects; Mathlib's Digraph allows loops and 2-cycles, which the predicate excludes
--   - encoding: contains … as a subgraph → ContainsSubgraph: an injective vertex map sending every arc of the ladder to an arc of T (not necessarily induced); reason: the usual meaning of subgraph; the ladders are drawn on vertices u1, …, uk, taken as Fin k with index i − 1
--   - encoding: Q: the vertex set partitioned into U0, U1, …, Uk → InQ: a center c and a block index blk : V → ℕ with U_j = blk⁻¹(j), U0 = {c}, blk ≤ k; reason: the same partitions
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Lemma 2.11, p.10

import Mathlib
import Definitions.Def_FASTournament_InQ
import Definitions.Def_FASTournament_MobiusFree

namespace FASTournament

/-- **Lemma 2.11.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Lemma 2.11, p.10: "Every tournament in Q is Möbius-free." -/
theorem lemma_2_11 {V : Type*} [Fintype V] (G : Digraph V) (hG : InQ G) :
    MobiusFree G := by sorry

end FASTournament
