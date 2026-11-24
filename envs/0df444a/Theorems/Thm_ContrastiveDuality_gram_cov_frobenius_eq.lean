-- Prove2me | Theorems.Thm_ContrastiveDuality_gram_cov_frobenius_eq
-- name    : ContrastiveDuality.gram_cov_frobenius_eq
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:31:25.300409+00:00
-- url     : https://prove2.me/theorems/2eee9bdc-be0d-4ae1-ba06-b24a90793928
-- title:
--   Theorem 3.3 (proof idea, p. 4): $\|K^TK\|_F^2=\|KK^T\|_F^2$
-- statement:
--   For every real matrix $\mathcal K\in\mathbb{R}^{M\times N}$, the Gram matrix and the (uncentred) covariance matrix of the embeddings have the same squared Frobenius norm:
--
--   $$\|\mathcal K^T\mathcal K\|_F^2=\|\mathcal K\mathcal K^T\|_F^2.$$
--
--   The paper names this identity as the fact on which the proof of Theorem 3.3 hinges: penalising all entries of the Gram matrix is the same as penalising all entries of $\mathcal K\mathcal K^T$.
-- source:
--   Garrido, Chen, Bardes, Najman and LeCun, On the duality between contrastive and non-contrastive self-supervised learning, arXiv:2206.02574v3 (ICLR 2023), Section 3, paragraph after Theorem 3.3, p. 4

import Mathlib
import Definitions.Def_ContrastiveDuality_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace ContrastiveDuality

theorem gram_cov_frobenius_eq {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ) :
    frobSq (Kᵀ * K) = frobSq (K * Kᵀ) := by sorry

end ContrastiveDuality
