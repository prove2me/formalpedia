-- Prove2me | Theorems.Thm_CycleLengthsExp_BetaGraph_lemma_4_1
-- name    : CycleLengthsExp.BetaGraph.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:24:20.842592+00:00
-- url     : https://prove2.me/theorems/d96792b1-8be2-422b-8c0e-40934eb49222
-- title:
--   Lemma 4.1 — a β-graph contains an induced subgraph on ≥ (1−β)n vertices with |N(U)| ≥ ((1−3β)/(2β))|U| for |U| ≤ βn
-- statement:
--   Let $\beta>0$ and let $G$ be a β-graph on $n$ vertices. Then $G$ contains a subgraph $G'$ on at least $(1-\beta)n$ vertices such that
--   $$|N_{G'}(U)|\ \ge\ \frac{1-3\beta}{2\beta}\,|U|\qquad\text{for every vertex set } U\subseteq V(G') \text{ with } |U|\le\beta n.$$
--
--   In other words, every β-graph contains a large $\bigl(\beta n,\tfrac{1-3\beta}{2\beta}\bigr)$-expander. This is the first step of the proof of Theorem 3: the subgraph $G'$ is the host graph in which trees are embedded.
--
--   **Formalization Note** $G'$ is taken to be the induced subgraph $G[S]$ on a vertex set $S$; for $U\subseteq S$ its external neighborhood is $N_G(U)\cap S$. This is no loss: adding the edges of $G$ inside $V(G')$ to any subgraph only enlarges $N_{G'}(U)$, and the proof itself deletes vertex sets, producing an induced subgraph (the next paragraph of the paper calls it "an induced subgraph"). Graphs are on the vertex set $\{0,\dots,n-1\}$ (`Fin n`).
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 15, Lemma 4.1

import Mathlib
import Definitions.Def_CycleLengthsExp_BetaGraph_Setting

namespace CycleLengthsExp.BetaGraph

/-- Lemma 4.1 (p. 15): a β-graph `G` on `n` vertices contains an induced subgraph `G' = G[S]`
on at least `(1 - β)n` vertices in which every `U ⊆ S` with `|U| ≤ βn` satisfies
`|N_{G'}(U)| ≥ ((1 - 3β)/(2β))|U|`. For `U ⊆ S`, `N_{G[S]}(U) = N_G(U) ∩ S`. -/
theorem lemma_4_1 (β : ℝ) (hβ : 0 < β) (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : IsBetaGraph β G) :
    ∃ S : Set (Fin n), (1 - β) * n ≤ S.ncard ∧
      ∀ U ⊆ S, (U.ncard : ℝ) ≤ β * n →
        (1 - 3 * β) / (2 * β) * U.ncard ≤ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S).ncard := by sorry

end CycleLengthsExp.BetaGraph
