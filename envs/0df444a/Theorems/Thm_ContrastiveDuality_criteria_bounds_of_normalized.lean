-- Prove2me | Theorems.Thm_ContrastiveDuality_criteria_bounds_of_normalized
-- name    : ContrastiveDuality.criteria_bounds_of_normalized
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T06:33:39.875696+00:00
-- url     : https://prove2.me/theorems/6366ed89-2259-4796-8834-9cdcbe8a023d
-- title:
--   Corollary 3.4.1: the criteria are close under one-sided normalization
-- statement:
--   Let $M,N\ge1$ and $\mathcal K\in\mathbb{R}^{M\times N}$.
--
--   1. If the embeddings are L2-normalized, $\|\mathcal K_{\cdot,i}\|_2=1$ for every $i$, then
--   $$L_{nc}-N+\frac{N^2}{M}\le L_c\le L_{nc}-N+N^2.$$
--   2. If the dimensions are L2-normalized, $\|\mathcal K_{j,\cdot}\|_2=1$ for every $j$, then
--   $$L_c-M+\frac{M^2}{N}\le L_{nc}\le L_c-M+M^2.$$
--
--   So, even when only one direction of the embedding matrix is normalized, the sample-contrastive and dimension-contrastive criteria cannot be arbitrarily far apart.
--
--   **Formalization Note** The batch size and embedding dimension are assumed positive, as in the paper's setting; all quantities are real numbers.
-- source:
--   Garrido, Chen, Bardes, Najman and LeCun, On the duality between contrastive and non-contrastive self-supervised learning, arXiv:2206.02574v3 (ICLR 2023), Section 3, Corollary 3.4.1, eqs. (6)-(7), p. 5

import Mathlib
import Definitions.Def_ContrastiveDuality_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace ContrastiveDuality

theorem criteria_bounds_of_normalized {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (K : Matrix (Fin M) (Fin N) ℝ) :
    ((∀ i, colNorm K i = 1) →
      nonContrastiveCriterion K - N + (N : ℝ) ^ 2 / M ≤ contrastiveCriterion K ∧
        contrastiveCriterion K ≤ nonContrastiveCriterion K - N + (N : ℝ) ^ 2) ∧
    ((∀ j, rowNorm K j = 1) →
      contrastiveCriterion K - M + (M : ℝ) ^ 2 / N ≤ nonContrastiveCriterion K ∧
        nonContrastiveCriterion K ≤ contrastiveCriterion K - M + (M : ℝ) ^ 2) := by sorry

end ContrastiveDuality
