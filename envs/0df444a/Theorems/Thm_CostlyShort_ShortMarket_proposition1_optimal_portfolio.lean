-- Prove2me | Theorems.Thm_CostlyShort_ShortMarket_proposition1_optimal_portfolio
-- name    : CostlyShort.ShortMarket.proposition1_optimal_portfolio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:28.161054+00:00
-- url     : https://prove2.me/theorems/c112358b-f6f2-49fa-bd7f-1485df047e0e
-- title:
--   Proposition 1, p. 17 — under (7) and φ ≥ γ the optimal portfolios of (8) are given by (9a)–(9b)
-- statement:
--   Let $\sigma_1,\sigma_2>0$ be the volatilities of the two risky assets, $\theta_1,\theta_2$ an agent's market prices of risk, and $\gamma,\phi$ the lending yield and shorting cost per unit of volatility. Assume condition (7), $\theta_2=\theta_1+\gamma$, and $\phi\ge\gamma$. Consider the mean-variance problem (8) with $\Phi=\phi\sigma_1$, $\Gamma=\gamma\sigma_1$:
--   $$\max_{p\in\mathbb R\times\mathbb R_+}\Big\{\Lambda(p_1;\Phi,\Gamma)+p_1\sigma_1\theta_1+p_2\sigma_2\theta_2-\tfrac12(p_1\sigma_1+p_2\sigma_2)^2\Big\}.$$
--   Then:
--
--   1. every portfolio of the form (9),
--   $$p_1\sigma_1=\mathbb 1_{\{\theta_2\ge0\}}x+\mathbb 1_{\{\theta_1+\phi\le0\}}(\theta_1+\phi),\qquad p_2\sigma_2=\mathbb 1_{\{\theta_2\ge0\}}(\theta_2-x),$$
--   with $0\le x\le\theta_2$ when $\theta_2\ge0$, is optimal;
--   2. if moreover $\phi>\gamma$, every optimal portfolio is of this form.
--
--   The proposition describes the agents' trading: with a positive net Sharpe ratio $\theta_2$ an agent goes long, splitting the efficient exposure $\theta_2$ between the two assets in any proportion; otherwise she shorts asset 1 exactly when $-(\theta_1+\phi)>0$, and holds only the riskless asset if not.
--
--   **Formalization Note** The paper states "the optimal portfolio satisfies (9)" under $\phi\ge\gamma$. At $\phi=\gamma$ the converse fails: with $\sigma_1=\sigma_2=1$ and $\theta_1=\gamma=\phi=0$, the portfolio $(-1,1)$ is optimal while (9) forces $(0,0)$. So the converse is stated under $\phi>\gamma$, and sufficiency under the printed $\phi\ge\gamma$. The paper's "$x_t$ is an arbitrary process" becomes an arbitrary real $x$ at the fixed state; its constraint $0\le x\le\theta_2$ is required only when $\theta_2\ge0$, since as printed it has no solution when $\theta_2<0$.
-- source:
--   Evgeniou, Hugonnier & Prieto, Asset Pricing with Costly Short Sales, SFI Research Paper N°22-21 (version of September 22, 2022), p. 17, Proposition 1, (9a)–(9b); proof p. 48

import Mathlib
import Definitions.Def_CostlyShort_ShortMarket_Setting

namespace CostlyShort.ShortMarket

theorem proposition1_optimal_portfolio (σ₁ σ₂ φ γ θ₁ θ₂ : ℝ)
    (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) (h7 : θ₂ = θ₁ + γ) (hφγ : γ ≤ φ) :
    (∀ p : ℝ × ℝ, IsProp1Portfolio σ₁ σ₂ φ θ₁ θ₂ p →
        IsOptimalFractions σ₁ σ₂ (φ * σ₁) (γ * σ₁) θ₁ θ₂ p) ∧
      (γ < φ → ∀ p : ℝ × ℝ, IsOptimalFractions σ₁ σ₂ (φ * σ₁) (γ * σ₁) θ₁ θ₂ p →
        IsProp1Portfolio σ₁ σ₂ φ θ₁ θ₂ p) := by sorry

end CostlyShort.ShortMarket
