-- Prove2me | Theorems.Thm_CorrClustBBC_Cautious_lemma_4
-- name    : CorrClustBBC.Cautious.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:39.477998+00:00
-- url     : https://prove2.me/theorems/5b665c2b-6309-4063-80fe-f6187da9feb5
-- title:
--   Lemma 4, p. 95 — a clustering whose clusters are all δ-clean (δ ≤ 1/4) makes at most 4∑rᵢ mistakes for some fractional packing
-- statement:
--   Let $G$ be a complete $\pm$-labelled graph on a finite vertex set $V$, let $\delta\le 1/4$ be real, and let $D$ be a clustering of $V$ in which every cluster is $\delta$-clean (in $G$). Then there is a fractional packing $w$ of erroneous triangles such that
--   $$m_D\ \le\ 4\sum_T w(T).$$
--
--   Combined with Lemma 3 this shows that a clustering made of clean clusters is within a factor $4$ of optimal (Corollary 5); the construction of the packing is what the analysis of Algorithm Cautious charges its internal mistakes to.
--
--   **Formalization Note** "Every cluster is $\delta$-clean" is stated as: for every vertex $v$, the cluster of $v$ is $\delta$-clean with respect to the whole vertex set.
--
--   Differences from the source:
--   - encoding: a finite list of erroneous triangles with positive weights rᵢ → a weight function w on vertex sets, nonnegative and nonzero only on erroneous triangles; reason: the same packings, absent triangles having weight 0.
--   - encoding: a clustering of V → a setoid on V, its clusters being the classes; reason: a clustering is a partition, and partitions are setoids.
-- source:
--   Bansal, Blum, Chawla, Correlation Clustering, Machine Learning 56 (2004) 89–113, p. 95, Lemma 4

import Mathlib
import Definitions.Def_CorrClustBBC_Cautious_Setting

namespace CorrClustBBC.Cautious
theorem lemma_4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (δ : ℝ) (hδ : δ ≤ 1 / 4) (D : Setoid V)
    (hD : ∀ v, IsClean G Finset.univ δ (classOf D v)) :
    ∃ w : Finset V → ℝ, IsFracPacking G w ∧ (mistakes G D.r : ℝ) ≤ 4 * ∑ T, w T := by sorry
end CorrClustBBC.Cautious
