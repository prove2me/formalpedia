-- Prove2me | Theorems.Thm_CVPricing_CertEquiv_det_coeff_matrix_pos
-- name    : CVPricing.CertEquiv.det_coeff_matrix_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:13:05.278555+00:00
-- url     : https://prove2.me/theorems/888f6f64-30b5-4815-b35f-735b8100f15c
-- title:
--   Proof of Proposition 1, p. 780 — the coefficient matrix of (12) has positive determinant
-- statement:
--   Let $0 < p_l \le p_1 < p_2 \le p_h$. The coefficient matrix of the linear system (12) in $(e_1, e_2)$ has determinant
--
--   $$\det\begin{pmatrix} p_2 - 2p_h & 2p_h - p_1 \\ p_1 - p_h & p_2 - p_h \end{pmatrix} = (p_2 - 2p_h)(p_2 - p_h) + (p_1 - p_h)(p_1 - 2p_h),$$
--
--   and this number is strictly positive.
--
--   Invertibility of this matrix is what makes the first two conditions of the event $A$ jointly satisfiable on a set of positive Lebesgue measure.
--
--   **Formalization Note** The proof assumes $p_1 < p_2$ without loss of generality; the statement is made under that ordering.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 780 (PDF 12), Appendix, proof of Proposition 1, the sentence after Eq. (12)

import Mathlib
import Definitions.Def_CVPricing_CertEquiv_Model

namespace CVPricing.CertEquiv

theorem det_coeff_matrix_pos (M : Model) {p₁ p₂ : ℝ} (hp₁ : M.pl ≤ p₁) (h12 : p₁ < p₂)
    (hp₂ : p₂ ≤ M.ph) :
    Matrix.det !![p₂ - 2 * M.ph, 2 * M.ph - p₁; p₁ - M.ph, p₂ - M.ph] =
        (p₂ - 2 * M.ph) * (p₂ - M.ph) + (p₁ - M.ph) * (p₁ - 2 * M.ph) ∧
      0 < (p₂ - 2 * M.ph) * (p₂ - M.ph) + (p₁ - M.ph) * (p₁ - 2 * M.ph) := by sorry

end CVPricing.CertEquiv
