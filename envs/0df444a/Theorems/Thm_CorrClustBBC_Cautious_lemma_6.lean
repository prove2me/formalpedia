-- Prove2me | Theorems.Thm_CorrClustBBC_Cautious_lemma_6
-- name    : CorrClustBBC.Cautious.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:25.165239+00:00
-- url     : https://prove2.me/theorems/c837397b-af71-4fbc-bbc2-e0f6c3d061a7
-- title:
--   Lemma 6, p. 96 — δ-Clean-Up: some clustering OPT′ with δ-clean non-singleton clusters has m_OPT′ ≤ (9/δ² + 1)·m_OPT
-- statement:
--   Let $G$ be a complete $\pm$-labelled graph on a finite vertex set $V$ and let $0<\delta<1$. For every clustering $D$ of $V$ there is a clustering $D'$ of $V$ in which every cluster with at least two vertices is $\delta$-clean (in $G$), and
--   $$m_{D'}\ \le\ \Big(\frac{9}{\delta^2}+1\Big)\,m_D .$$
--   Applied to an optimal clustering $D=\mathrm{OPT}$, this gives the clustering $\mathrm{OPT}'$ of the paper, with $m_{\mathrm{OPT}'}\le (9/\delta^2+1)\,m_{\mathrm{OPT}}$.
--
--   $\mathrm{OPT}'$ is the near-optimal clean target that Algorithm Cautious is shown to recover (Theorem 7); with $\delta=1/44$ this lemma supplies the factor $9/\delta^2+1$ in Theorem 13.
--
--   Differences from the source:
--   - reading: δ unspecified (Lemma 6 precedes the standing assumption δ = 1/44) → every real δ with 0 < δ < 1; reason: the proof uses δ < 1 ("as δ < 1", p. 97) and 9/δ² needs δ ≠ 0; δ = 1/44 is the instance used later.
--   - generalization: OPT (an optimal clustering) → every clustering D; reason: the procedure δ-Clean-Up and its accounting never use optimality; D = OPT is the page's statement.
--   - encoding: "non-singleton cluster" → a class with at least two elements, δ-clean with respect to the whole vertex set; reason: same notion.
-- source:
--   Bansal, Blum, Chawla, Correlation Clustering, Machine Learning 56 (2004) 89–113, p. 96, Lemma 6 (proof pp. 96–97)

import Mathlib
import Definitions.Def_CorrClustBBC_Cautious_Setting

namespace CorrClustBBC.Cautious
theorem lemma_6 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (D : Setoid V) :
    ∃ D' : Setoid V, NonsingletonClean G δ D' ∧
      (mistakes G D'.r : ℝ) ≤ (9 / δ ^ 2 + 1) * (mistakes G D.r : ℝ) := by sorry
end CorrClustBBC.Cautious
