-- Prove2me | Theorems.Thm_ContrastiveDuality_doubly_normalized_criteria
-- name    : ContrastiveDuality.doubly_normalized_criteria
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T06:32:40.716991+00:00
-- url     : https://prove2.me/theorems/fa0997d3-dc69-4525-b4d5-1563dd0a389b
-- title:
--   Theorem 3.3 (consequence, p. 4): for doubly normalized $K$, $L_{nc}=L_c+N-M$
-- statement:
--   Let $\mathcal K\in\mathbb{R}^{M\times N}$ have all columns and all rows of unit Euclidean norm: $\|\mathcal K_{\cdot,i}\|_2=1$ for every $i$ and $\|\mathcal K_{j,\cdot}\|_2=1$ for every $j$. Then
--
--   $$L_{nc}=L_c+N-M.$$
--
--   Since the two hypotheses force $N=M$ (see the note), the constant $N-M$ is always $0$, so under double normalization the two criteria are equal.
--
--   **Formalization Note** $N-M$ is computed in the real numbers. The two hypotheses together give $\|\mathcal K\|_F^2=N=M$, so they can hold only when $N=M$; for example the identity matrix satisfies them.
-- source:
--   Garrido, Chen, Bardes, Najman and LeCun, On the duality between contrastive and non-contrastive self-supervised learning, arXiv:2206.02574v3 (ICLR 2023), Section 3, paragraph after Theorem 3.3, p. 4

import Mathlib
import Definitions.Def_ContrastiveDuality_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace ContrastiveDuality

theorem doubly_normalized_criteria {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ)
    (hcol : ∀ i, colNorm K i = 1) (hrow : ∀ j, rowNorm K j = 1) :
    nonContrastiveCriterion K = contrastiveCriterion K + (N : ℝ) - (M : ℝ) := by sorry

end ContrastiveDuality
