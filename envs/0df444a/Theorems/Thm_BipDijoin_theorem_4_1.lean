-- Prove2me | Theorems.Thm_BipDijoin_theorem_4_1
-- name    : BipDijoin.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:49:13.197265+00:00
-- url     : https://prove2.me/theorems/b3e77cb6-dae2-4dfa-8470-662ccc3cbd75
-- title:
--   Theorem 4.1 — a relaxed end decomposition yields a minimum dijoin and a maximum dicut packing (time clause carried by the goal)
-- statement:
--   Let $D$ be a bipartite digraph whose arcs all point from $L$ to $R$, with underlying graph $G$, and let $\mathcal E$ be a relaxed bipartite end decomposition of $G$ with recorded internal matchings $P^i=M^i\cap E(H^i[U^i])$. Then
--   $$B=\bigcup_i P^i$$
--   is a minimum dijoin of $D$, and some maximum dicut packing of $D$ has exactly $|B|$ members.
--
--   The construction is Algorithm 5: going backwards through the decomposition, $B^i=P^i\cup\mathrm{lift}_i(B^{i+1})$ and the dicut family adds the in-stars $\delta^-(r)$, $r\in U^i_R$, of a source end or the out-stars $\delta^+(\ell)$, $\ell\in U^i_L$, of a sink end. The theorem reduces bipartite dijoin to computing a relaxed end decomposition, where the matchings need not be maximum.
--
--   **Formalization Note** The decomposition is supplied as records; $H^i$ is recomputed by contracting, and the matchings $M^i$ need not be maximum.
--
--   Differences from the source:
--   - reading: a minimum dijoin and a maximum dicut packing of D can be obtained from ℰ with no asymptotic time overhead → the union of the recorded P^i is a minimum dijoin, and a maximum dicut packing with that many members exists; the time clause is posed as part of theorem_1_1, whose program must output both; reason: the structural content is what the reduction needs; the running time of Algorithm 5 matters only inside the algorithm of Theorem 1.1
--   - encoding: lifting maps lift_i from quotients to H^i → contraction keeps edge identities, so each lift is the identity on edges and B = ⋃ P^i; reason: same dijoin and same lifted dicuts
--   - encoding: the sequence of triples (H^i, M^i, U^i) → the records (s_i, U^i, P^i) with H^i recomputed by contraction and M^i asserted to exist; representatives named N₀ + i; reason: Lean data for the same sequence
--   - generalization: G 2-edge-connected (the standing reduction of §2.1, p.3, and the hypothesis of Theorem 2.3, whose proof App. B reuses) → every well-formed bipartite multigraph that has a relaxed end decomposition; reason: the proof of Theorem 2.3 (App. A, pp.45–46) never uses 2-edge-connectivity; on 2-edge-connected graphs the Lean statement is the source's
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), Theorem 4.1, p.8 (PDF p.10); proof App. A–B, pp.45–46 (PDF pp.47–48)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph
import Definitions.Def_BipDijoin_IsDicut
import Definitions.Def_BipDijoin_IsPartialDecomp

set_option autoImplicit false

namespace BipDijoin

/-- **Theorem 4.1** (Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6),
p.8 = PDF p.10; proof App. A–B, pp.45–46 = PDF pp.47–48), structural part. "Let D = (L⊎R, A) be an
unweighted bipartite digraph whose arcs all point from L to R, and let ℰ be a relaxed bipartite
end decomposition of its underlying undirected graph G. A minimum dijoin and a maximum dicut
packing of D can be obtained from ℰ with no asymptotic time overhead."

For every well-formed bipartite multigraph `G` and every relaxed bipartite end decomposition of
`G` (records `(sᵢ, Uⁱ, Pⁱ)`, representatives `N₀, N₀ + 1, …`), the union `B = ⋃ᵢ Pⁱ` of the
recorded internal matchings is a minimum dijoin of `G`, and some maximum dicut packing of `G` has
exactly `|B|` members.

Construction (Algorithm 5, p.45): `Bᵏ ← ∅, Cᵏ ← ∅`; for `i = k−1, …, 0`: `Pⁱ ← Mⁱ ∩ E(Hⁱ[Uⁱ])`,
`Bⁱ ← Pⁱ ∪ liftᵢ(Bⁱ⁺¹)`; if `Uⁱ` is a source strong end, `Sⁱ ← {δ⁻_{Hⁱ}(r) : r ∈ Uⁱ_R}`, else
`Sⁱ ← {δ⁺_{Hⁱ}(l) : l ∈ Uⁱ_L}`; `Cⁱ ← Sⁱ ∪ liftᵢ(Cⁱ⁺¹)`; return `(B⁰, C⁰)`.

**Formalization Note.** The time clause ("with no asymptotic time overhead") is carried by the
goal `theorem_1_1`. Contraction keeps edge identities, so every lifting map is the identity on
edges and `B` is literally `⋃ᵢ Pⁱ`. -/
theorem theorem_4_1 (G : BipGraph) (hG : G.WF) (N₀ : ℕ) (recs : List Rec)
    (h : IsDecomp false G N₀ recs) :
    G.IsMinDijoin (dijoinOf recs) ∧
      ∃ F, G.IsMaxDicutPacking F ∧ F.length = (dijoinOf recs).card := by sorry

end BipDijoin
