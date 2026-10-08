-- Prove2me | Theorems.Thm_DemandSubstitution_Correlation_proposition2_profit_decreasing_in_correlation
-- name    : DemandSubstitution.Correlation.proposition2_profit_decreasing_in_correlation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:34.297958+00:00
-- url     : https://prove2.me/theorems/a180f08b-c191-425c-a41c-88b3e779e020
-- title:
--   Proposition 2, p. 7 — under N(μ, Σ) demand the centralized expected profit decreases in every correlation ρ_ij, for fixed or optimally adjusted Q
-- statement:
--   Fix the substitution model and a mean vector $m\in\mathbb R^n$. Let $\Sigma^1,\Sigma^2$ be positive semidefinite covariance matrices such that $\Sigma^2$ is obtained from $\Sigma^1$ by raising the covariance $\sigma_{ij}$ of two distinct products $i\ne j$ (symmetrically) while every other entry, in particular every variance, stays fixed. For a covariance matrix $\Sigma$ let
--   $$\pi^{\Sigma}(Q) = \mathbb E\sum_i\big[u_iD^s_i - u_i(D^s_i-Q_i)^+ - o_i(Q_i-D^s_i)^+\big],\qquad D\sim N(m,\Sigma),$$
--   be the centralized expected profit (1). Then:
--
--   1. (**stocking quantities held fixed**) for every $Q\ge 0$,
--   $$\pi^{\Sigma^2}(Q)\le\pi^{\Sigma^1}(Q);$$
--   2. (**stocking quantities adjusted optimally**) if $Q^1$ maximizes $\pi^{\Sigma^1}$ and $Q^2$ maximizes $\pi^{\Sigma^2}$ over the nonnegative stocking vectors, then
--   $$\pi^{\Sigma^2}(Q^2)\le\pi^{\Sigma^1}(Q^1).$$
--
--   That is, the retailer's profit is decreasing in every correlation coefficient $\rho_{ij}$, whether stocking quantities are held fixed or re-optimized as correlation changes.
--
--   **Formalization Note.** Correlations are encoded through covariances with fixed variances (raising $\rho_{ij}$ with $\sigma_{ii},\sigma_{jj}$ fixed is raising $\sigma_{ij}$). The paper argues "adjusted optimally" through the total derivative $d\pi/d\rho_{ij}$ along a differentiable optimal path; the formal statement compares the optimal values for every pair of maximizers instead, which needs no differentiability. "Decreasing" is read weakly ($\le$). The positive-support assumption of §2 is not used, as in the paper.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), p. 7, Proposition 2; proof pp. 7–8

import Mathlib
import Definitions.Def_DemandSubstitution_Correlation_Setting

namespace DemandSubstitution.Correlation

theorem proposition2_profit_decreasing_in_correlation {n : ℕ} (M : Model n) (m : Fin n → ℝ)
    (S₁ S₂ : Matrix (Fin n) (Fin n) ℝ) (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef)
    (i j : Fin n) (hraise : RaisesCovariance S₁ S₂ i j) :
    (∀ Q : Fin n → ℝ, (∀ k, 0 ≤ Q k) → centralProfit M m S₂ Q ≤ centralProfit M m S₁ Q) ∧
      ∀ Q₁ Q₂ : Fin n → ℝ, IsCentralOptimal M m S₁ Q₁ → IsCentralOptimal M m S₂ Q₂ →
        centralProfit M m S₂ Q₂ ≤ centralProfit M m S₁ Q₁ := by sorry

end DemandSubstitution.Correlation
