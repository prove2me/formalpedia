-- Prove2me | Theorems.Thm_ContrastiveDuality_norm_pow_four_bounds
-- name    : ContrastiveDuality.norm_pow_four_bounds
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:33:13.596237+00:00
-- url     : https://prove2.me/theorems/81d09a03-d407-4de5-bcb0-6a127f71397d
-- title:
--   Lemma 3.4: bounds on the sum of fourth powers of row and column norms
-- statement:
--   Let $M,N\ge1$, let $\mathcal K\in\mathbb{R}^{M\times N}$ and let $a\in\mathbb{R}$.
--
--   1. If the embeddings are normalized so that $\|\mathcal K_{\cdot,i}\|_2=a$ for every $i$, then
--   $$\frac{N^2}{M}a^4\le\sum_{j=1}^M\|\mathcal K_{j,\cdot}\|_2^4\le N^2a^4.$$
--   2. If the dimensions are normalized so that $\|\mathcal K_{j,\cdot}\|_2=a$ for every $j$, then
--   $$\frac{M^2}{N}a^4\le\sum_{i=1}^N\|\mathcal K_{\cdot,i}\|_2^4\le M^2a^4.$$
--
--   A norm constraint in one direction of the embedding matrix thus constrains the norms in the other direction.
--
--   **Formalization Note** The batch size $N$ and the embedding dimension $M$ are assumed positive, as they are in the paper's setting; the bounds divide by $M$ and by $N$.
-- source:
--   Garrido, Chen, Bardes, Najman and LeCun, On the duality between contrastive and non-contrastive self-supervised learning, arXiv:2206.02574v3 (ICLR 2023), Section 3, Lemma 3.4, eqs. (4)-(5), p. 5; restated as Lemma C.5, eqs. (48)-(49), proof eqs. (50)-(51), pp. 17-18

import Mathlib
import Definitions.Def_ContrastiveDuality_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace ContrastiveDuality

theorem norm_pow_four_bounds {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (K : Matrix (Fin M) (Fin N) ℝ) (a : ℝ) :
    ((∀ i, colNorm K i = a) →
      (N : ℝ) ^ 2 / M * a ^ 4 ≤ ∑ j, rowNorm K j ^ 4 ∧
        ∑ j, rowNorm K j ^ 4 ≤ (N : ℝ) ^ 2 * a ^ 4) ∧
    ((∀ j, rowNorm K j = a) →
      (M : ℝ) ^ 2 / N * a ^ 4 ≤ ∑ i, colNorm K i ^ 4 ∧
        ∑ i, colNorm K i ^ 4 ≤ (M : ℝ) ^ 2 * a ^ 4) := by sorry

end ContrastiveDuality
