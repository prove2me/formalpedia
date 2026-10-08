-- Prove2me | Theorems.Thm_BoydADMM_L1_covsel_root_spec
-- name    : BoydADMM.L1.covsel_root_spec
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:07:09.129183+00:00
-- url     : https://prove2.me/theorems/2c91e894-a783-4aa1-83e7-ac3abba567a9
-- title:
--   §6.5, p. 47 — $\tilde X_{ii}=(\lambda_i+\sqrt{\lambda_i^2+4\rho})/(2\rho)$ is positive and solves $\rho t-1/t=\lambda_i$
-- statement:
--   Let $\rho>0$ and $\mu\in\mathbb R$. The number
--   $$t=\frac{\mu+\sqrt{\mu^2+4\rho}}{2\rho}$$
--   is positive and satisfies
--   $$\rho\,t-\frac1t=\mu .$$
--
--   This is the scalar step of the closed-form X-update for sparse inverse covariance selection: after diagonalizing $\rho(Z^k-U^k)-S$, each diagonal entry $\tilde X_{ii}$ of the solution must be a positive root of $\rho t-1/t=\lambda_i$.
--
--   **Formalization Note** The book's eigenvalue $\lambda_i$ is called $\mu$ (`λ` is a Lean keyword).
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 47, §6.5

import Mathlib
import Definitions.Def_BoydADMM_L1_CovSel

open Matrix

namespace BoydADMM.L1

/-- §6.5, p. 47: for `ρ > 0` the quadratic-formula value `t = (μ + √(μ² + 4ρ))/(2ρ)` is positive
and solves `ρ t − 1/t = μ` (`μ` is the book's eigenvalue `λ_i`). -/
theorem covsel_root_spec (ρ μ : ℝ) (hρ : 0 < ρ) :
    0 < covselRoot ρ μ ∧ ρ * covselRoot ρ μ - 1 / covselRoot ρ μ = μ := by sorry

end BoydADMM.L1
