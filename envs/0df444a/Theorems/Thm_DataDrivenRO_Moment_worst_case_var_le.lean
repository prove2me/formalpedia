-- Prove2me | Theorems.Thm_DataDrivenRO_Moment_worst_case_var_le
-- name    : DataDrivenRO.Moment.worst_case_var_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:24:09.252925+00:00
-- url     : https://prove2.me/theorems/aa5615ec-4489-46b1-9e80-043b51dd105b
-- title:
--   (34), p. 25 — moment-region value at risk upper bound
-- statement:
--   Fix $R\ge0$, nonnegative moment thresholds $\Gamma_1,\Gamma_2$, estimates $\hat\mu,\hat\Sigma$, and a risk level $0<\varepsilon<1$. For every probability law $P$ in the supported moment region $\mathcal P^{CS}$ and every vector $v\in\mathbb R^d$,
--
--   $$
--   \operatorname{VaR}^P_{\varepsilon}(v)\le
--   \hat\mu^\top v+\Gamma_1\|v\|_2+
--   \sqrt{\frac{1-\varepsilon}{\varepsilon}}
--   \sqrt{v^\top(\hat\Sigma+\Gamma_2I)v}.
--   $$
--
--   The bound transfers uncertainty in the mean and covariance to a bound on every linear projection's upper quantile. It is the probability input to Theorem 10.
--
--   **Formalization Note** Equation (34) prints equality after a supremum over $P$. The region here also restricts support to the radius-$R$ ball, and the source does not establish attainment of that equality under the support restriction. This statement takes only the upper-bound direction needed by Theorem 10. The law's ball support ensures the moments are genuine integrals.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, (34), p. 25

import Mathlib
import Definitions.Def_DataDrivenRO_Moment_Setting

namespace DataDrivenRO.Moment

/-- The upper-bound direction of (34), p. 25. The printed equality is not
asserted because the region also restricts distributions to a support ball. -/
theorem worst_case_var_le {d : ℕ} (R Γ₁ Γ₂ : ℝ)
    (μhat : Fin d → ℝ) (Shat : Matrix (Fin d) (Fin d) ℝ)
    (hR : 0 ≤ R) (hΓ₁ : 0 ≤ Γ₁) (hΓ₂ : 0 ≤ Γ₂)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ P ∈ PCS R Γ₁ Γ₂ μhat Shat, ∀ v : Fin d → ℝ,
      VaR P ε v ≤ csValue μhat Shat Γ₁ Γ₂ ε v := by sorry

end DataDrivenRO.Moment
