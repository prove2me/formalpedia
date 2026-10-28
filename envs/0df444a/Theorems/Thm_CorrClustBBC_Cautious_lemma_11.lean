-- Prove2me | Theorems.Thm_CorrClustBBC_Cautious_lemma_11
-- name    : CorrClustBBC.Cautious.lemma_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:58.366016+00:00
-- url     : https://prove2.me/theorems/035da91c-c26d-4a04-bdc5-d7eafbf40ed6
-- title:
--   Lemma 11, p. 99 (corrected: ≤ for <, and a clause on positive mistakes) — Cautious makes no more external mistakes than OPT′
-- statement:
--   Let $\delta=1/44$ and let $G$ be a complete $\pm$-labelled graph on a finite vertex set $V$. Let $D$ be a clustering of $V$ whose clusters with at least two vertices are $\delta$-clean in $G$ (for instance $\mathrm{OPT}'$ of Lemma 6), and let $S$ be the set of vertices forming singleton clusters of $D$. Consider any run of Algorithm Cautious on $G$, with output clustering $\mathcal A$ and final singleton set $Z$. Then
--   1. the external mistakes of Cautious (mistakes with an endpoint in $Z$) are at most the external mistakes of $D$ (mistakes with an endpoint in $S$):
--   $$\#\{\text{mistakes of }\mathcal A\text{ meeting }Z\}\ \le\ \#\{\text{mistakes of }D\text{ meeting }S\};$$
--   2. the positive mistakes of Cautious are at most the positive mistakes of $D$:
--   $$m^+_{\mathcal A}\ \le\ m^+_D .$$
--
--   Clause 1 is the paper's bound on the mistakes at the leftover singletons $Z$. Clause 2 extends it to every positive mistake, which together with the corrected Lemma 12 and Lemma 6 gives Theorem 13.
--
--   Differences from the source:
--   - correction: "less than" → "at most" (≤); reason: the strict inequality fails on the all-+ complete graph on 5 vertices, where OPT = OPT′ = {V}, Cautious outputs {V}, Z = S = ∅ and both counts are 0. The proof (p. 100) proves ≤.
--   - generalization: one clause added, the positive mistakes of Cautious are at most those of D; reason: Lemma 12 as printed is false (18-vertex counterexample, see Lemma 12), and the repaired proof of Theorem 13 bounds the positive internal mistakes this way; the clause is the page's own argument for Lemma 11 applied to all positive mistakes, and dropping it leaves the page's statement (clause 1).
--   - generalization: OPT′ → every clustering D whose clusters with at least two vertices are δ-clean in G; reason: the proof uses only this property of OPT′, which OPT′ has by Lemma 6.
--   - reading: "repeat until no vertices are left or until all the produced sets A(v) are empty" → the run may stop exactly when every remaining vertex, tried as the pivot, has some execution of steps 1(a)–(c) producing ∅; reason: the phrase is ambiguous; this is the reading under which "all the produced sets are empty" refers to every remaining vertex.
--   - reading: N⁺(v), δ-goodness and the "y ∈ V" of step 1(c) in every iteration after the first → taken in the graph induced on the vertices not yet clustered (the current set R of the run); reason: step 2 deletes A(v) "from the set of vertices" before repeating, and the proof of Theorem 7 (p. 99) argues in "the remaining graph G \ (⋃_{ℓ<i} A_ℓ)".
--   - encoding: the output of Cautious → the output clustering of any run of the run relation, over all pivot choices and removal orders; reason: the algorithm's choices are arbitrary, so the lemma holds for every choice.
-- source:
--   Bansal, Blum, Chawla, Correlation Clustering, Machine Learning 56 (2004) 89–113, p. 99, Lemma 11 (proof p. 100)

import Mathlib
import Definitions.Def_CorrClustBBC_Cautious_Setting

namespace CorrClustBBC.Cautious
theorem lemma_11 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Setoid V) (hD : NonsingletonClean G δ44 D)
    (L : List (Finset V × Finset V × Finset V)) (Z : Finset V) (hrun : Run G Finset.univ L Z) :
    extMistakes G (sameCluster L) Z ≤ extMistakes G D.r (singletonsOf D) ∧
      posMistakes G (sameCluster L) ≤ posMistakes G D.r := by sorry
end CorrClustBBC.Cautious
