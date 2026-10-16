-- Prove2me | Theorems.Thm_ClimateImpact_Uncertainty_prop6_iv
-- name    : ClimateImpact.Uncertainty.prop6_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:41.678609+00:00
-- url     : https://prove2.me/theorems/306375bd-35e3-47a6-be25-d1a73057739c
-- title:
--   Proposition 6(iv), p. 35 — if θᵀN^g = 0, then y_λ = 1 for all λ > 0, so portfolios and expected returns do not depend on λ
-- statement:
--   Let $\Sigma$ be positive definite, $0<\alpha<1$, $\gamma^r,\gamma^g>0$, and fix the externality vector $\theta=\theta_t(\psi_t)$ of a given emission schedule. Let $\lambda\mapsto y_\lambda$ be the solution map of (20): for every $\lambda>0$, $y_\lambda>0$ solves (20). Write $N^g=\alpha(\mathbf 1+\frac{1}{\gamma^r}\Sigma^{-1}\theta)$ for the green portfolio without climate uncertainty, $N^{g,\lambda}=\alpha(\mathbf 1+\frac{y_\lambda}{\gamma^r}\Sigma^{-1}\theta)$ for the one with uncertainty level $\lambda$, and $\mu_\lambda=\gamma^*\Sigma\mathbf 1-\alpha y_\lambda\theta$ for the expected returns (18).
--
--   If $\theta^\top N^g=0$, then for every $\lambda>0$:
--
--   $$
--   y_\lambda=1,\qquad N^{g,\lambda}=N^g,\qquad \mu_\lambda=\mu_1.
--   $$
--
--   So climate uncertainty affects neither the green portfolio nor the expected returns.
--
--   **Formalization Note** The solution map enters only through the hypothesis that each $y_\lambda$ solves (20). "Do not depend on the level of climate uncertainty" is stated as equality with the values at $y=1$, for every $\lambda>0$. $\alpha\in(0,1)$ is free; $\Sigma$ is positive definite.
-- source:
--   SSRN 3562534 (25 Jun 2021), Proposition 6(iv), p. 35; §6.4, p. 70

import Mathlib
import Definitions.Def_ClimateImpact_Uncertainty_Portfolio
open Matrix

namespace ClimateImpact.Uncertainty

/-- Proposition 6(iv) (p. 35): if the green portfolio without climate uncertainty has neutral
climate externalities, `y_λ = 1` for all `λ > 0`, so the green portfolio and the expected returns
do not depend on `λ`. -/
theorem prop6_iv {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (α γr γg : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hγr : 0 < γr) (hγg : 0 < γg)
    (θ : Fin n → ℝ)
    (Y : ℝ → ℝ) (hY : ∀ lam : ℝ, 0 < lam → IsYLambda S α γr γg lam θ (Y lam))
    (hzero : θ ⬝ᵥ greenPortfolio S α γr θ 1 = 0) :
    ∀ lam : ℝ, 0 < lam →
      Y lam = 1 ∧ greenPortfolio S α γr θ (Y lam) = greenPortfolio S α γr θ 1 ∧
        expectedReturn S α γr γg θ (Y lam) = expectedReturn S α γr γg θ 1 := by sorry

end ClimateImpact.Uncertainty
