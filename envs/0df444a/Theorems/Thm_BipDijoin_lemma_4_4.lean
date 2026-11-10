-- Prove2me | Theorems.Thm_BipDijoin_lemma_4_4
-- name    : BipDijoin.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:49:24.144522+00:00
-- url     : https://prove2.me/theorems/909a3001-5e05-4905-9a6f-88817a3f036e
-- title:
--   Lemma 4.4, clauses 1–2 — contracting the fitted strong end and all small fitted strong ends (procedure-free; time clause carried by the goal)
-- statement:
--   Let $G$ be a bipartite multigraph, $\sigma\in\mathbb N$, $M'$ a matching of $G$ and $U$ a nontrivial strong end of $G$ fitted by $M'$. Let $\mathcal W$ consist of $U$ and of every nontrivial strong end of $G$ of size at most $\sigma$ that is fitted by $M'$. Contract the members of $\mathcal W$ one by one, in any order, without rematching, and let $M''=M'\setminus\bigcup_{W\in\mathcal W}E(G[W])$. Then:
--
--   1. the contractions form a partial relaxed end decomposition of $G$, ending at some graph $G'$, whose records carry $M'\cap E(G[W])$;
--   2. $M''$ is a matching of $G'$, and every nontrivial strong end of $G'$ of size at most $\sigma$ contains a vertex of $V(G')\setminus V(M'')$.
--
--   In the paper, Local-Cleanup finds exactly the members of $\mathcal W$ by bounded searches from the old terminal set $T$, using the hypothesis that $T$ meets every small strong end; this restores the invariant that every small strong end contains an unmatched vertex.
--
--   **Formalization Note** $\mathcal W$ is enumerated by a list without repetition; its members are disjoint SCCs of $G_{M'}$.
--
--   Differences from the source:
--   - generalization: T is the unmatched set of a matching M and meets every nontrivial strong end of size at most σ; U is returned by Local-Strong-End → no hypothesis on T or M; U is any nontrivial strong end fitted by M′; reason: the conclusion holds without the hypothesis, so the Lean statement specializes to the source's
--   - reading: there is a procedure Local-Cleanup(G, M′, T, U, σ) that contracts U and possibly other nontrivial strong ends fitted by M′; its search work is Õ(σ²|T|) → the contraction of exactly U and every strong end of size at most σ fitted by M′, in any order; the time clause is posed as part of theorem_1_1 and theorem_4_2; reason: the proof (p.11) shows the searches from T certify exactly these ends; their cost matters only inside those algorithms
--   - encoding: contracted vertices without names → representatives named N₀, N₀ + 1, … for any N₀ above every vertex name; reason: Lean needs names
--   - generalization: G the current 2-edge-connected quotient of Algorithm 1 (the standing reduction of §2.1, p.3) → every well-formed bipartite multigraph; reason: the structural argument of the proof (p.11) uses only Definition 2.1; on 2-edge-connected graphs the Lean statement is the source's
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), Lemma 4.4, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph
import Definitions.Def_BipDijoin_IsMatching
import Definitions.Def_BipDijoin_IsStrongEnd
import Definitions.Def_BipDijoin_IsPartialDecomp

set_option autoImplicit false

namespace BipDijoin

/-- **Lemma 4.4**, clauses 1–2, procedure-free form (Nalam–Saranurak, STOC 2027 submission
(manuscript sha256 382f85e4…7fea6), p.11 = PDF p.13). "Let T be the unmatched set of a matching M
of G, and suppose that T intersects every nontrivial strong end of size at most σ. Let M′ be a
matching fitting a nontrivial strong end U returned by Local-Strong-End. There is a procedure
Local-Cleanup(G, M′, T, U, σ) that outputs a partial relaxed end decomposition, its resulting graph
G′, and a matching M″ such that 1. the procedure contracts U and possibly other nontrivial strong
ends fitted by M′, without further rematching; and 2. every nontrivial strong end of G′ of size at
most σ intersects V(G′) \ V(M″)."

Let `G` be a well-formed bipartite multigraph, `σ ∈ ℕ`, `M′` a matching of `G` and `U` a
(nontrivial) strong end of `G` fitted by `M′`. Let `𝒲` consist of `U` and of every strong end of
`G` of size at most `σ` fitted by `M′`, and let `ℓ` enumerate `𝒲` without repetition, in any
order. Contracting the members of `ℓ` in order (representatives `N₀, N₀ + 1, …`, `N₀` above all
vertex ids), without rematching, gives a partial relaxed end decomposition ending at some `G′`
whose records carry `Pⁱ = M′ ∩ E(G[Uⁱ])`; `M″ = M′ ∖ ⋃_{W ∈ 𝒲} E(G[W])` is a matching of `G′`; and
every strong end of `G′` of size at most `σ` contains a vertex not covered by `M″`.

**Formalization Note.** The proof of the lemma (p.11) shows that Local-Cleanup, run from the old
terminal set `T`, contracts exactly `U` and the strong ends of size at most `σ` fitted by `M′`;
the statement is posed for that set directly, so `T`, `M` and the hypothesis on `T` drop out. The
search-time clause `Õ(σ²|T|)` is carried by the goal `theorem_1_1` and by `theorem_4_2`. -/
theorem lemma_4_4 (G : BipGraph) (hG : G.WF) (σ : ℕ) (M' : Finset ℕ) (hM' : G.IsMatching M')
    (U : Finset ℕ) (hU : G.IsStrongEnd U) (hfit : G.Fits M' U) (N₀ : ℕ)
    (hN₀ : ∀ v ∈ G.V, v < N₀) (ℓ : List (Finset ℕ)) (hnd : ℓ.Nodup)
    (hℓ : ∀ W, W ∈ ℓ ↔ (W = U ∨ (G.IsStrongEnd W ∧ G.Fits M' W ∧ W.card ≤ σ))) :
    ∃ (recs : List Rec) (G' : BipGraph), recs.map Rec.U = ℓ ∧
      (∀ r ∈ recs, r.P = M' ∩ (G.induced r.U).E) ∧
      IsPartialDecomp false G N₀ recs G' ∧
      G'.IsMatching (M' \ G.internalEdges ℓ) ∧
      ∀ W, G'.IsStrongEnd W → W.card ≤ σ →
        ∃ v ∈ W, ¬ G'.covered (M' \ G.internalEdges ℓ) v := by sorry

end BipDijoin
