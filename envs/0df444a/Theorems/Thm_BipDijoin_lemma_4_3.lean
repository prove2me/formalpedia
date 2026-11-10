-- Prove2me | Theorems.Thm_BipDijoin_lemma_4_3
-- name    : BipDijoin.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:49:12.723094+00:00
-- url     : https://prove2.me/theorems/af001c34-1384-4eb8-98e4-08e7a6584c2c
-- title:
--   Lemma 4.3, clauses 1–3 — Global-Strong-End contracts every fitted extremal SCC (time clause carried by the goal)
-- statement:
--   Let $G$ be a 2-edge-connected bipartite multigraph and $M$ a maximum matching of $G$. Let $\mathcal C$ be the set of all nontrivial source and sink SCCs of $G_M$, and contract its members one by one in any order, recording $(G,\,M\cap E(G[U]),\,U)$ and removing $E(G[U])$ from $M$ (Algorithm 2). Then:
--
--   1. the records form a partial relaxed end decomposition of $G$;
--   2. it ends at a graph $G'$;
--   3. $M'=M\setminus\bigcup_{U\in\mathcal C}E(G[U])$ is a matching of $G'$, and every strong end of $G'$ contains a vertex left unmatched by $M'$.
--
--   The lemma sets up the invariant of the main algorithm: after a global step, every remaining strong end contains an unmatched vertex, so a matching repair is needed before the next contraction.
--
--   **Formalization Note** The order of contraction is arbitrary, as in the proof ("contraction can be applied in any order").
--
--   Differences from the source:
--   - reading: there exists an algorithm Global-Strong-End with outputs 1–3 in time Ô(|E|) → the outputs of the paper's Algorithm 2 for every maximum matching and every order of 𝒞, with the records P^i = M ∩ E(G[U^i]); the time clause is posed as part of theorem_1_1 and theorem_4_2; reason: the lemma is proved by Algorithm 2; its running time matters only inside those algorithms
--   - encoding: contracted vertices without names → representatives named N₀, N₀ + 1, … for any N₀ above every vertex name; reason: Lean needs names
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), Lemma 4.3, p.9 (PDF p.11); Algorithm 2 and proof, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph
import Definitions.Def_BipDijoin_IsMatching
import Definitions.Def_BipDijoin_IsStrongEnd
import Definitions.Def_BipDijoin_IsPartialDecomp

set_option autoImplicit false

namespace BipDijoin

/-- **Lemma 4.3**, clauses 1–3 (Nalam–Saranurak, STOC 2027 submission (manuscript sha256
382f85e4…7fea6), p.9 = PDF p.11; Algorithm 2 and proof, p.12 = PDF p.14). "There exists an algorithm
Global-Strong-End takes as input a bipartite graph G = (L ∪ R, E) that is 2-edge-connected and
outputs: 1. Parital end decomposition 2. Resulting graph G′ 3. Partial matching M′ of G′ such that
every strong end contains an unmatched vertex with respect to M′ in time Ô(|E|)."

Algorithm 2 computes a maximum matching `M`, takes the set `𝒞` of all nontrivial source and sink
SCCs of `G_M`, and contracts its members one by one, recording `(G, M ∩ E[U], U)` and removing
`E[U]` from `M`. The lemma, for this algorithm: let `G` be a well-formed 2-edge-connected bipartite
multigraph, `M` a maximum matching, and `ℓ` any list enumerating `𝒞` without repetition. Then
contracting the members of `ℓ` in order (representatives `N₀, N₀ + 1, …`, `N₀` above all vertex
ids) gives a partial relaxed end decomposition ending at some `G′`, whose records carry
`Pⁱ = M ∩ E(G[Uⁱ])`; `M′ = M ∖ ⋃_{U ∈ 𝒞} E(G[U])` is a matching of `G′`; and every strong end of
`G′` contains a vertex not covered by `M′`.

**Formalization Note.** The time clause `Ô(|E|)` is carried by the goal `theorem_1_1` and by
`theorem_4_2`. The order of `ℓ` is arbitrary ("contraction can be applied in any order"). -/
theorem lemma_4_3 (G : BipGraph) (hG : G.WF) (h2 : G.TwoEdgeConnected) (M : Finset ℕ)
    (hM : G.IsMaxMatching M) (N₀ : ℕ) (hN₀ : ∀ v ∈ G.V, v < N₀) (ℓ : List (Finset ℕ))
    (hnd : ℓ.Nodup)
    (hℓ : ∀ U, U ∈ ℓ ↔
      (2 ≤ U.card ∧ (IsSourceSCC (G.altArc M) G.V U ∨ IsSinkSCC (G.altArc M) G.V U))) :
    ∃ (recs : List Rec) (G' : BipGraph), recs.map Rec.U = ℓ ∧
      (∀ r ∈ recs, r.P = M ∩ (G.induced r.U).E) ∧
      IsPartialDecomp false G N₀ recs G' ∧
      G'.IsMatching (M \ G.internalEdges ℓ) ∧
      ∀ U, G'.IsStrongEnd U → ∃ v ∈ U, ¬ G'.covered (M \ G.internalEdges ℓ) v := by sorry

end BipDijoin
