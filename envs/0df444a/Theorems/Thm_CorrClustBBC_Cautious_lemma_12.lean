-- Prove2me | Theorems.Thm_CorrClustBBC_Cautious_lemma_12
-- name    : CorrClustBBC.Cautious.lemma_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:09.501401+00:00
-- url     : https://prove2.me/theorems/03d165f3-4c56-48f1-8e6f-26bad2f356b9
-- title:
--   Lemma 12, p. 100 (corrected: negative mistakes only) — the negative mistakes of Cautious are at most 4·m_OPT
-- statement:
--   Let $G$ be a complete $\pm$-labelled graph on a finite vertex set $V$. Consider any run of Algorithm Cautious ($\delta=1/44$) on $G$, with output clustering $\mathcal A$. Then for every clustering $D$ of $V$,
--   $$m^-_{\mathcal A}\ \le\ 4\,m_D ,$$
--   where $m^-_{\mathcal A}$ is the number of negative mistakes of $\mathcal A$ (pairs labelled $-$ placed in a common cluster). Equivalently, $m^-_{\mathcal A}\le 4\,m_{\mathrm{OPT}}$.
--
--   Every negative mistake of Cautious is internal, since the vertices of $Z$ are singletons. With Lemma 11 (positive mistakes) and Lemma 6, this bound gives Theorem 13.
--
--   Differences from the source:
--   - correction: the internal mistakes of Cautious are ≤ 4·m_OPT → the negative mistakes of Cautious are ≤ 4·m_OPT; reason: the printed statement is false. Take n = 18, K = {0,…,14} a + clique, u = 15 adjacent (+) to all of K and to y₁ = 16, y₂ = 17, with y₁y₂ also +, all other pairs −. Picking 0 first, u is the only 3δ-bad vertex of N⁺(0) = K ∪ {u}, so A′₁ = K; u is not 7δ-good w.r.t. K, so A₁ = K; then A₂ = {u, y₁, y₂} and Z = ∅. The run makes 15 internal mistakes (u–K), while {K ∪ {u}, {y₁, y₂}} makes 2, and 15 > 4·2. The printed proof applies Corollary 5 to clusters that are clean only in their own remaining graphs. The printed constant 4 is kept.
--   - encoding: m_OPT → m_D for every clustering D; reason: m_OPT is the minimum over all clusterings, so the two statements are equivalent.
--   - reading: "repeat until no vertices are left or until all the produced sets A(v) are empty" → the run may stop exactly when every remaining vertex, tried as the pivot, has some execution of steps 1(a)–(c) producing ∅; reason: the phrase is ambiguous; this is the reading under which "all the produced sets are empty" refers to every remaining vertex.
--   - reading: N⁺(v), δ-goodness and the "y ∈ V" of step 1(c) in every iteration after the first → taken in the graph induced on the vertices not yet clustered (the current set R of the run); reason: step 2 deletes A(v) "from the set of vertices" before repeating, and the proof of Theorem 7 (p. 99) argues in "the remaining graph G \ (⋃_{ℓ<i} A_ℓ)".
--   - encoding: the output of Cautious → the output clustering of any run of the run relation, over all pivot choices and removal orders; reason: the algorithm's choices are arbitrary, so the lemma holds for every choice.
-- source:
--   Bansal, Blum, Chawla, Correlation Clustering, Machine Learning 56 (2004) 89–113, p. 100, Lemma 12

import Mathlib
import Definitions.Def_CorrClustBBC_Cautious_Setting

namespace CorrClustBBC.Cautious
theorem lemma_12 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : List (Finset V × Finset V × Finset V)) (Z : Finset V) (hrun : Run G Finset.univ L Z)
    (D : Setoid V) :
    negMistakes G (sameCluster L) ≤ 4 * mistakes G D.r := by sorry
end CorrClustBBC.Cautious
