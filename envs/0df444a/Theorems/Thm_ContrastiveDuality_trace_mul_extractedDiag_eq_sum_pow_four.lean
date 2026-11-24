-- Prove2me | Theorems.Thm_ContrastiveDuality_trace_mul_extractedDiag_eq_sum_pow_four
-- name    : ContrastiveDuality.trace_mul_extractedDiag_eq_sum_pow_four
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:30:41.430952+00:00
-- url     : https://prove2.me/theorems/6eaa482e-92c0-4e7b-8151-8cf914be63c2
-- title:
--   Theorem C.4 (proof, p. 17): $\mathrm{tr}(K^TK\,\mathrm{diag}(K^TK))=\sum_i\|K_{\cdot,i}\|_2^4$
-- statement:
--   Let $\mathcal K\in\mathbb{R}^{M\times N}$. Since $(\mathcal K^T\mathcal K)_{i,i}=\|\mathcal K_{\cdot,i}\|_2^2$ and $(\mathcal K\mathcal K^T)_{j,j}=\|\mathcal K_{j,\cdot}\|_2^2$,
--
--   $$\operatorname{tr}\big(\mathcal K^T\mathcal K\operatorname{diag}(\mathcal K^T\mathcal K)\big)=\sum_{i=1}^N\|\mathcal K_{\cdot,i}\|_2^4,\qquad \operatorname{tr}\big(\mathcal K\mathcal K^T\operatorname{diag}(\mathcal K\mathcal K^T)\big)=\sum_{j=1}^M\|\mathcal K_{j,\cdot}\|_2^4.$$
--
--   This is the step of the proof of Theorem 3.3 that turns the diagonal corrections into sums of fourth powers of column and row norms.
-- source:
--   Garrido, Chen, Bardes, Najman and LeCun, On the duality between contrastive and non-contrastive self-supervised learning, arXiv:2206.02574v3 (ICLR 2023), Appendix C, proof of Theorem C.4 (= Theorem 3.3), sentence after eq. (46), p. 17

import Mathlib
import Definitions.Def_ContrastiveDuality_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace ContrastiveDuality

theorem trace_mul_extractedDiag_eq_sum_pow_four {M N : ℕ} (K : Matrix (Fin M) (Fin N) ℝ) :
    Matrix.trace (Kᵀ * K * extractedDiag (Kᵀ * K)) = ∑ i, colNorm K i ^ 4 ∧
    Matrix.trace (K * Kᵀ * extractedDiag (K * Kᵀ)) = ∑ j, rowNorm K j ^ 4 := by sorry

end ContrastiveDuality
