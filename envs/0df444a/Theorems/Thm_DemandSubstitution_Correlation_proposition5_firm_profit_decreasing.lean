-- Prove2me | Theorems.Thm_DemandSubstitution_Correlation_proposition5_firm_profit_decreasing
-- name    : DemandSubstitution.Correlation.proposition5_firm_profit_decreasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:34.692989+00:00
-- url     : https://prove2.me/theorems/394a513d-7695-4033-a170-1cf5c6e35213
-- title:
--   Proposition 5, p. 10 — under N(μ, Σ) demand each firm's expected profit π_k decreases in every correlation ρ_ij, stocking quantities fixed
-- statement:
--   Fix the substitution model and a mean vector $m\in\mathbb R^n$. Let $\Sigma^1,\Sigma^2$ be positive semidefinite covariance matrices such that $\Sigma^2$ is obtained from $\Sigma^1$ by raising the covariance $\sigma_{ij}$ of two distinct products $i\ne j$ (symmetrically) while every other entry, in particular every variance, stays fixed; equivalently, the correlation $\rho_{ij}$ rises with all variances fixed. Let $\pi_k^{\Sigma}(Q) = \mathbb E\big[u_k D^s_k - u_k(D^s_k-Q_k)^+ - o_k(Q_k-D^s_k)^+\big]$ be the expected profit (9) of firm $k$ when $D\sim N(m,\Sigma)$. Then for every stocking vector $Q\ge 0$ and every firm $k$,
--   $$\pi_k^{\Sigma^2}(Q) \le \pi_k^{\Sigma^1}(Q).$$
--
--   In the competitive model, every firm's expected profit therefore decreases (weakly) as any demand correlation rises, as long as all stocking quantities are kept fixed.
--
--   **Formalization Note.** The paper speaks of correlations $\rho_{ij}=\sigma_{ij}/\sqrt{\sigma_{ii}\sigma_{jj}}$; with the variances fixed, raising $\rho_{ij}$ is raising $\sigma_{ij}$, so the statement is phrased with covariances (it also covers a zero variance, where $\sigma_{ij}=0$ is forced). "Decreasing" is read weakly ($\le$). The positive-support assumption of §2 is not used, as in the paper.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), p. 10, Proposition 5

import Mathlib
import Definitions.Def_DemandSubstitution_Correlation_Setting

namespace DemandSubstitution.Correlation

theorem proposition5_firm_profit_decreasing {n : ℕ} (M : Model n) (m : Fin n → ℝ)
    (S₁ S₂ : Matrix (Fin n) (Fin n) ℝ) (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef)
    (i j : Fin n) (hraise : RaisesCovariance S₁ S₂ i j)
    (Q : Fin n → ℝ) (hQ : ∀ k, 0 ≤ Q k) (k : Fin n) :
    firmProfit M m S₂ Q k ≤ firmProfit M m S₁ Q k := by sorry

end DemandSubstitution.Correlation
