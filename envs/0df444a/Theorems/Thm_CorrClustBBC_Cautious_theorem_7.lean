-- Prove2me | Theorems.Thm_CorrClustBBC_Cautious_theorem_7
-- name    : CorrClustBBC.Cautious.theorem_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:32.968979+00:00
-- url     : https://prove2.me/theorems/e73dfefe-62ea-4739-a7c9-79ef71d03b0f
-- title:
--   Theorem 7, p. 97 (corrected: 11δ-clean in the remaining graph) — every C′ⱼ lies inside some Aᵢ, and each Aᵢ is 11δ-clean
-- statement:
--   Let $\delta=1/44$ and let $G$ be a complete $\pm$-labelled graph on a finite vertex set $V$. Let $D$ be a clustering of $V$ whose clusters with at least two vertices are $\delta$-clean in $G$ (for instance $\mathrm{OPT}'$ of Lemma 6). Consider any run of Algorithm Cautious on $G$, producing clusters $A_1,A_2,\dots$, where $A_i$ is formed in the remaining graph on $R_i=V\setminus(A_1\cup\dots\cup A_{i-1})$. Then:
--   1. every cluster $C'_j$ of $D$ with at least two vertices satisfies $C'_j\subseteq A_i$ for some $i$;
--   2. every $A_i$ is $11\delta$-clean in the graph induced on $R_i$:
--   $$|N^+_{R_i}(v)\cap A_i|\ge(1-11\delta)|A_i| \quad\text{and}\quad |N^+_{R_i}(v)\cap(R_i\setminus A_i)|\le 11\delta|A_i| \qquad (v\in A_i).$$
--
--   The theorem says that Cautious recovers every non-singleton cluster of $\mathrm{OPT}'$ and produces only clean clusters; it is the structural core of the approximation guarantee (Theorem 13).
--
--   Differences from the source:
--   - correction: each Aᵢ is 11δ-clean (in G) → each Aᵢ is 11δ-clean in the remaining graph G \ (A₁ ∪ … ∪ Aᵢ₋₁) it was formed in; reason: false in G. Take n = 46, K = {0,…,43} a + clique, x = 44 adjacent (+) to {0,…,21} and to y = 45, all other pairs −; the run picking 30 and then x gives A₁ = K and A₂ = {x, y}, and in G x has 22 > 11δ·2 positive neighbours outside A₂. The proof (p. 99) argues in the remaining graph.
--   - generalization: OPT′ → every clustering D whose clusters with at least two vertices are δ-clean in G; reason: the proof uses only this property of OPT′, which OPT′ has by Lemma 6.
--   - reading: "repeat until no vertices are left or until all the produced sets A(v) are empty" → the run may stop exactly when every remaining vertex, tried as the pivot, has some execution of steps 1(a)–(c) producing ∅; reason: the phrase is ambiguous; this is the reading under which "all the produced sets are empty" refers to every remaining vertex.
--   - reading: N⁺(v), δ-goodness and the "y ∈ V" of step 1(c) in every iteration after the first → taken in the graph induced on the vertices not yet clustered (the current set R of the run); reason: step 2 deletes A(v) "from the set of vertices" before repeating, and the proof of Theorem 7 (p. 99) argues in "the remaining graph G \ (⋃_{ℓ<i} A_ℓ)".
--   - encoding: the clusters A₁, A₂, … output by Cautious → the clusters recorded by any run of the run relation, over all pivot choices and removal orders; reason: the algorithm picks an arbitrary vertex and removes an arbitrary bad vertex, so the theorem holds for every choice.
-- source:
--   Bansal, Blum, Chawla, Correlation Clustering, Machine Learning 56 (2004) 89–113, p. 97, Theorem 7 (proof pp. 98–99)

import Mathlib
import Definitions.Def_CorrClustBBC_Cautious_Setting

namespace CorrClustBBC.Cautious
theorem theorem_7 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Setoid V) (hD : NonsingletonClean G δ44 D)
    (L : List (Finset V × Finset V × Finset V)) (Z : Finset V) (hrun : Run G Finset.univ L Z) :
    (∀ v, 2 ≤ (classOf D v).card → ∃ p ∈ L, classOf D v ⊆ p.2.1) ∧
      ∀ p ∈ L, IsClean G p.2.2 (11 * δ44) p.2.1 := by sorry
end CorrClustBBC.Cautious
