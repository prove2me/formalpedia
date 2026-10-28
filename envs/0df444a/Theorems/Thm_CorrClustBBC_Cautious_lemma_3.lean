-- Prove2me | Theorems.Thm_CorrClustBBC_Cautious_lemma_3
-- name    : CorrClustBBC.Cautious.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:30.250534+00:00
-- url     : https://prove2.me/theorems/0cb79a66-c83f-4d63-b8f0-8b2d3045780d
-- title:
--   Lemma 3, p. 94 — the weight of any fractional packing of erroneous triangles is at most the number of mistakes of any clustering
-- statement:
--   Let $G$ be a complete graph on a finite vertex set $V$ whose edges are labelled $+$ or $-$. Let $w$ be a fractional packing of erroneous triangles: nonnegative weights on triangles with two positive edges and one negative edge, such that the triangles containing any fixed pair of vertices carry total weight at most $1$. Then for every clustering $D$ of $V$, with $m_D$ mistakes,
--   $$\sum_{T} w(T)\ \le\ m_D .$$
--   In particular the weight of every packing is a lower bound on $m_{\mathrm{OPT}}$, the number of mistakes of an optimal clustering.
--
--   This is the lower bound on OPT against which the mistakes of clean clusterings are charged (Lemma 4, Corollary 5) and through which the negative mistakes of Algorithm Cautious are bounded (Lemma 12).
--
--   **Formalization Note** A packing is a weight function on all vertex subsets that is nonnegative and nonzero only on erroneous triangles; triangles of weight zero are absent from the page's list.
--
--   Differences from the source:
--   - generalization: ∑ rᵢ ≤ OPT (an optimal clustering) → ∑ w(T) ≤ m_D for every clustering D; reason: the proof only uses that every clustering makes a mistake on each erroneous triangle; D = OPT is the page's statement.
--   - encoding: a finite list of erroneous triangles with positive weights rᵢ → a weight function w on vertex sets, nonnegative and nonzero only on erroneous triangles; reason: the same packings, absent triangles having weight 0.
-- source:
--   Bansal, Blum, Chawla, Correlation Clustering, Machine Learning 56 (2004) 89–113, p. 94, Lemma 3

import Mathlib
import Definitions.Def_CorrClustBBC_Cautious_Setting

namespace CorrClustBBC.Cautious
theorem lemma_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset V → ℝ) (hw : IsFracPacking G w) (D : Setoid V) :
    ∑ T, w T ≤ (mistakes G D.r : ℝ) := by sorry
end CorrClustBBC.Cautious
