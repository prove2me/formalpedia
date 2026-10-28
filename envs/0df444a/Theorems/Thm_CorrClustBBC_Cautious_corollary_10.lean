-- Prove2me | Theorems.Thm_CorrClustBBC_Cautious_corollary_10
-- name    : CorrClustBBC.Cautious.corollary_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:41.562+00:00
-- url     : https://prove2.me/theorems/aecb76de-262f-4c67-90b1-39b463eb6373
-- title:
--   Corollary 10, p. 98 — after the removal step, A(v) never holds vertices of two distinct non-singleton clusters of OPT′
-- statement:
--   Let $\delta=1/44$ and let $G$ be a complete $\pm$-labelled graph on a finite vertex set $V$. Let $D$ be a clustering of $V$ whose clusters with at least two vertices are $\delta$-clean in $G$ (for instance $\mathrm{OPT}'$ of Lemma 6). Consider any run of Algorithm Cautious on $G$, with any choice of pivots and any removal order, producing clusters $A_1, A_2,\dots$, and let $A'_i$ be the set left after the removal step 1(b) in the iteration that produced $A_i$. Then for every $i$ and all $u,v\in A'_i$ whose clusters in $D$ have at least two vertices,
--   $$D(u)=D(v).$$
--
--   Corollary 10 is the key step of Theorem 7's proof: each set produced by the removal step meets at most one non-singleton cluster of $\mathrm{OPT}'$.
--
--   **Formalization Note** The statement covers every iteration that produced a nonempty cluster. An iteration in the final phase, which produces $\emptyset$, has an empty removal result, for which the claim is vacuous.
--
--   Differences from the source:
--   - generalization: OPT′ → every clustering D whose clusters with at least two vertices are δ-clean in G; reason: the proof uses only this property of OPT′, which OPT′ has by Lemma 6.
--   - reading: "repeat until no vertices are left or until all the produced sets A(v) are empty" → the run may stop exactly when every remaining vertex, tried as the pivot, has some execution of steps 1(a)–(c) producing ∅; reason: the phrase is ambiguous; this is the reading under which "all the produced sets are empty" refers to every remaining vertex.
--   - reading: N⁺(v), δ-goodness and the "y ∈ V" of step 1(c) in every iteration after the first → taken in the graph induced on the vertices not yet clustered (the current set R of the run); reason: step 2 deletes A(v) "from the set of vertices" before repeating, and the proof of Theorem 7 (p. 99) argues in "the remaining graph G \ (⋃_{ℓ<i} A_ℓ)".
--   - encoding: "after every application of the removal step 1b" → for the removal result A′ᵢ recorded with every produced cluster of a run of the run relation, over all pivot choices and removal orders; reason: the algorithm is nondeterministic; iterations producing ∅ have A′ = ∅, where the claim is vacuous.
-- source:
--   Bansal, Blum, Chawla, Correlation Clustering, Machine Learning 56 (2004) 89–113, p. 98, Corollary 10 (Algorithm Cautious p. 97)

import Mathlib
import Definitions.Def_CorrClustBBC_Cautious_Setting

namespace CorrClustBBC.Cautious
theorem corollary_10 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Setoid V) (hD : NonsingletonClean G δ44 D)
    (L : List (Finset V × Finset V × Finset V)) (Z : Finset V) (hrun : Run G Finset.univ L Z) :
    ∀ p ∈ L, ∀ u ∈ p.1, ∀ v ∈ p.1, 2 ≤ (classOf D u).card → 2 ≤ (classOf D v).card →
      D.r u v := by sorry
end CorrClustBBC.Cautious
