-- Prove2me | Theorems.Thm_ClimateImpact_Uncertainty_y_lambda_exists_unique
-- name    : ClimateImpact.Uncertainty.y_lambda_exists_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T10:57:35.457753+00:00
-- url     : https://prove2.me/theorems/38acb07a-7ad1-46aa-88c3-8fdfdb57f9b0
-- title:
--   §6.4, proof of Propositions 5 and 6, p. 69 — for every λ > 0 equation (20) has exactly one positive solution y_λ
-- statement:
--   Fix a date and drop its subscript. Let $\Sigma$ be a positive definite covariance matrix, $0<\alpha<1$, $\gamma^r,\gamma^g>0$, and let $\theta\in\mathbb R^n$ be the vector of climate externalities for a fixed emission schedule. Then for every $\lambda>0$ there is exactly one $y>0$ with
--
--   $$
--   y=\exp\Big\{-\frac{\alpha\gamma^g}{\lambda}\Big(\mathbf 1^\top\theta+\frac{y}{\gamma^r}\,\theta^\top\Sigma^{-1}\theta\Big)\Big\}.
--   $$
--
--   This is the factor $y_\lambda$ of Proposition 5, through which climate uncertainty enters prices and portfolios (footnote 23).
--
--   **Formalization Note** $\alpha$ is a free parameter in $(0,1)$; the relation $\alpha=\gamma^r/(\gamma^r+\gamma^g)$ is not needed. Positive definiteness of $\Sigma$ is assumed because Mathlib's inverse of a singular matrix is $0$.
-- source:
--   SSRN 3562534 (25 Jun 2021), §6.4, proof of Propositions 5 and 6, (47), p. 69; (20), p. 34; footnote 23, p. 34

import Mathlib
import Definitions.Def_ClimateImpact_Uncertainty_Portfolio
open Matrix

namespace ClimateImpact.Uncertainty

/-- Proof of Propositions 5 and 6 (p. 69): for every `λ > 0`, equation (20) has exactly one
positive solution `y_λ`. -/
theorem y_lambda_exists_unique {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (α γr γg : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hγr : 0 < γr) (hγg : 0 < γg)
    (θ : Fin n → ℝ) :
    ∀ lam : ℝ, 0 < lam → ∃! y : ℝ, IsYLambda S α γr γg lam θ y := by sorry

end ClimateImpact.Uncertainty
