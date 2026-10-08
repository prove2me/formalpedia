-- Prove2me | Theorems.Thm_BoydADMM_L1_covsel_X_update
-- name    : BoydADMM.L1.covsel_X_update
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:21:36.998012+00:00
-- url     : https://prove2.me/theorems/634069f9-03d6-4340-82fd-851d3e0a1828
-- title:
--   §6.5, p. 47 — the covariance-selection X-update is $Q\,\mathrm{diag}\bigl((\lambda_i+\sqrt{\lambda_i^2+4\rho})/(2\rho)\bigr)\,Q^T$
-- statement:
--   Let $S,Z,U\in\mathbb R^{n\times n}$ with $S$ and $Z-U$ symmetric, and let $\rho>0$. Let $Q\in\mathbb R^{n\times n}$ with $Q^TQ=QQ^T=I$ and $\mu_1,\dots,\mu_n\in\mathbb R$ satisfy
--   $$\rho(Z-U)-S=Q\,\mathrm{diag}(\mu_1,\dots,\mu_n)\,Q^T .$$
--   Put
--   $$X=Q\,\mathrm{diag}\Bigl(\frac{\mu_1+\sqrt{\mu_1^2+4\rho}}{2\rho},\dots,\frac{\mu_n+\sqrt{\mu_n^2+4\rho}}{2\rho}\Bigr)\,Q^T .$$
--   Then $X$ is symmetric positive definite, and it is the unique minimizer over the symmetric positive definite matrices $X'\in\mathbb S^n_{++}$ of
--   $$\operatorname{Tr}(SX')-\log\det X'+\frac\rho2\|X'-Z+U\|_F^2 .$$
--
--   With $Z=Z^k$ and $U=U^k$ this is the X-update of ADMM for sparse inverse covariance selection, minimize $\operatorname{Tr}(SX)-\log\det X+\lambda\|X\|_1$: the only update of the chapter that is neither a linear solve nor a thresholding, it costs one symmetric eigenvalue decomposition.
--
--   **Formalization Note** The book's eigenvalues $\lambda_i$ are called $\mu_i$. The statement holds for every orthogonal $Q$ and diagonal factor with $\rho(Z-U)-S=Q\,\mathrm{diag}(\mu)\,Q^T$, not just one chosen by Mathlib. The symmetry of $S$ (an empirical covariance $(1/N)\sum_ia_ia_i^T$) and of $Z-U$ (the ADMM iterates are symmetric) is an explicit hypothesis; $S$ is not required to be positive semidefinite. The minimization is over `Matrix.PosDef`, the domain of $\log\det$ (p. 46); singular matrices are not competitors. $\|\cdot\|_F^2$ is the sum of squared entries.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 47, §6.5 (X-update in closed form); objective on p. 46

import Mathlib
import Definitions.Def_BoydADMM_L1_Basic
import Definitions.Def_BoydADMM_L1_CovSel

open Matrix

namespace BoydADMM.L1

/-- §6.5, p. 47 (the goal): let `S` and `Z − U` be symmetric, `ρ > 0`, and
`ρ(Z − U) − S = Q diag(μ) Qᵀ` with `QᵀQ = QQᵀ = I`. Then `X = Q X̃ Qᵀ`,
`X̃_ii = (μ_i + √(μ_i² + 4ρ))/(2ρ)`, is positive definite and is the unique minimizer of
`Tr(SX) − log det X + (ρ/2)‖X − Z + U‖_F²` over the positive definite matrices. -/
theorem covsel_X_update {n : ℕ} (S Z U Q : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) (μ : Fin n → ℝ)
    (hρ : 0 < ρ) (hS : S.IsSymm) (hZU : (Z - U).IsSymm)
    (hQ₁ : Qᵀ * Q = 1) (hQ₂ : Q * Qᵀ = 1)
    (hdecomp : ρ • (Z - U) - S = Q * Matrix.diagonal μ * Qᵀ) :
    IsUniqueMinimizerOn (covselXObjective S Z U ρ) {X | X.PosDef} (covselX ρ Q μ) := by sorry

end BoydADMM.L1
