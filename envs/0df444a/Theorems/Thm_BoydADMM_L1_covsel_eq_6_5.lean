-- Prove2me | Theorems.Thm_BoydADMM_L1_covsel_eq_6_5
-- name    : BoydADMM.L1.covsel_eq_6_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:21:08.809979+00:00
-- url     : https://prove2.me/theorems/0fc15471-d68f-4e03-9ff4-ee497b2a5895
-- title:
--   (6.5), p. 47 — $X=Q\tilde XQ^T$ is positive definite and satisfies $\rho X-X^{-1}=\rho(Z^k-U^k)-S$
-- statement:
--   Let $S,Z,U\in\mathbb R^{n\times n}$, $\rho>0$, let $Q\in\mathbb R^{n\times n}$ satisfy $Q^TQ=QQ^T=I$, and let $\mu_1,\dots,\mu_n\in\mathbb R$ be such that
--   $$\rho(Z-U)-S=Q\,\Lambda\,Q^T,\qquad \Lambda=\mathrm{diag}(\mu_1,\dots,\mu_n).$$
--   Put $\tilde X=\mathrm{diag}(\tilde X_{11},\dots,\tilde X_{nn})$ with $\tilde X_{ii}=(\mu_i+\sqrt{\mu_i^2+4\rho})/(2\rho)$, and $X=Q\tilde XQ^T$. Then $X$ is positive definite and
--   $$\rho X-X^{-1}=\rho(Z-U)-S. \tag{6.5}$$
--
--   Equation (6.5) is the first-order optimality condition of the X-update in ADMM for sparse inverse covariance selection, so this says that the book's eigenvalue construction produces a positive definite solution of it.
--
--   **Formalization Note** $Z,U$ stand for $Z^k,U^k$; the eigenvalues $\lambda_i$ are called $\mu_i$. The statement quantifies over every orthogonal $Q$ and diagonal $\Lambda$ with $\rho(Z-U)-S=Q\Lambda Q^T$, not over one decomposition chosen by Mathlib; such a decomposition exists whenever $\rho(Z-U)-S$ is symmetric, and the identity forces it to be symmetric, so no symmetry hypothesis on $S$ or $Z-U$ is needed here. $X^{-1}$ is Mathlib's matrix inverse, the true inverse since $X$ is positive definite.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 47, §6.5, (6.5)

import Mathlib
import Definitions.Def_BoydADMM_L1_CovSel

open Matrix

namespace BoydADMM.L1

/-- §6.5, (6.5), p. 47: if `ρ > 0`, `Q` is orthogonal (`QᵀQ = QQᵀ = I`) and
`ρ(Z − U) − S = Q diag(μ) Qᵀ`, then `X = Q X̃ Qᵀ` with `X̃_ii = (μ_i + √(μ_i² + 4ρ))/(2ρ)` is
positive definite and satisfies `ρX − X⁻¹ = ρ(Z − U) − S`. -/
theorem covsel_eq_6_5 {n : ℕ} (S Z U Q : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) (μ : Fin n → ℝ)
    (hρ : 0 < ρ) (hQ₁ : Qᵀ * Q = 1) (hQ₂ : Q * Qᵀ = 1)
    (hdecomp : ρ • (Z - U) - S = Q * Matrix.diagonal μ * Qᵀ) :
    (covselX ρ Q μ).PosDef ∧ ρ • covselX ρ Q μ - (covselX ρ Q μ)⁻¹ = ρ • (Z - U) - S := by sorry

end BoydADMM.L1
