-- Prove2me | Theorems.Thm_BalancedPrices_WeakExtension_case_2_constant
-- name    : BalancedPrices.WeakExtension.case_2_constant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:03:10.5262+00:00
-- url     : https://prove2.me/theorems/a2beca6e-18c7-42f7-803e-1c77420d0df7
-- title:
--   Appendix A, Case 2, p. 560 — if β₁ + β₂ ≥ 1/α and β₂ < 1/(2α), then (1 − αβ₂)/(1 + αβ₁) ≥ 1/(α(2β₁ + 4β₂))
-- statement:
--   Let $\alpha>0$ and $\beta_1,\beta_2\ge0$ with
--   $$\beta_1+\beta_2\ \ge\ \frac1\alpha\qquad\text{and}\qquad \beta_2\ <\ \frac1{2\alpha}.$$
--   Then
--   $$\frac{1}{\alpha(2\beta_1+4\beta_2)} \ \le\ \frac{1-\alpha\beta_2}{1+\alpha\beta_1}.$$
--
--   This is the last step of Case 2 of the proof of Theorem 3.5: it shows that the guarantee $(1-\alpha\beta_2)/(1+\alpha\beta_1)$ obtained in Case 2 is at least the uniform guarantee $1/(\alpha(2\beta_1+4\beta_2))$ claimed by the theorem.
--
--   **Formalization Note.** A statement about real numbers only. The hypotheses make $2\beta_1+4\beta_2>0$, so the left side is not a division by zero.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), p. 560, Appendix A (proof of Theorem 3.5), Case 2, last step

import Mathlib

namespace BalancedPrices.WeakExtension

theorem case_2_constant (α β₁ β₂ : ℝ) (hα : 0 < α) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (hsum : 1 / α ≤ β₁ + β₂) (hcase : β₂ < 1 / (2 * α)) :
    1 / (α * (2 * β₁ + 4 * β₂)) ≤ (1 - α * β₂) / (1 + α * β₁) := by sorry

end BalancedPrices.WeakExtension
