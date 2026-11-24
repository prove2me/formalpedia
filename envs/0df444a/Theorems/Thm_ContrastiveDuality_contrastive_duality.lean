-- Prove2me | Theorems.Thm_ContrastiveDuality_contrastive_duality
-- name    : ContrastiveDuality.contrastive_duality
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:31:58.785311+00:00
-- url     : https://prove2.me/theorems/c11294ff-71d6-4340-9fc3-c2ffb1225b65
-- title:
--   Theorem 3.3: equivalence of the sample-contrastive and dimension-contrastive criteria
-- statement:
--   Let $\mathcal K\in\mathbb{R}^{M\times N}$ be an embedding matrix for a batch of size $N$ and embedding dimension $M$, with no further assumption. Then the sample-contrastive criterion $L_c=\|\mathcal K^T\mathcal K-\operatorname{diag}(\mathcal K^T\mathcal K)\|_F^2$ and the dimension-contrastive criterion $L_{nc}=\|\mathcal K\mathcal K^T-\operatorname{diag}(\mathcal K\mathcal K^T)\|_F^2$ satisfy
--
--   $$L_{nc}+\sum_{j=1}^M\|\mathcal K_{j,\cdot}\|_2^4=L_c+\sum_{i=1}^N\|\mathcal K_{\cdot,i}\|_2^4.$$
--
--   The two criteria therefore differ only by the fourth powers of the row and column norms of $\mathcal K$, which is the precise sense in which the paper calls them equivalent up to row and column normalization.
--
--   **Formalization Note** The paper's verbal claim that the criteria are "equivalent up to row and column normalization" is formalised as the identity (3), which is the mathematical content of the theorem.
-- source:
--   Garrido, Chen, Bardes, Najman and LeCun, On the duality between contrastive and non-contrastive self-supervised learning, arXiv:2206.02574v3 (ICLR 2023), Section 3, Theorem 3.3, eq. (3), p. 4; restated as Theorem C.4, eq. (39), proof eqs. (40)-(47), p. 17

import Mathlib
import Definitions.Def_ContrastiveDuality_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace ContrastiveDuality

theorem contrastive_duality {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ) :
    nonContrastiveCriterion K + ∑ j, rowNorm K j ^ 4 =
      contrastiveCriterion K + ∑ i, colNorm K i ^ 4 := by sorry

end ContrastiveDuality
