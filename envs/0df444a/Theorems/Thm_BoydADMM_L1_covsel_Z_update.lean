-- Prove2me | Theorems.Thm_BoydADMM_L1_covsel_Z_update
-- name    : BoydADMM.L1.covsel_Z_update
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:21:44.62455+00:00
-- url     : https://prove2.me/theorems/f4cdffd9-1eb3-4c4e-84f2-9669367000c9
-- title:
--   §6.5, p. 47 — the covariance-selection Z-update is elementwise soft thresholding $S_{\lambda/\rho}(X^{k+1}_{ij}+U^k_{ij})$
-- statement:
--   Let $\lambda\ge0$, $\rho>0$ and $X,U\in\mathbb R^{n\times n}$. The matrix $Z^\star$ with entries
--   $$Z^\star_{ij}=S_{\lambda/\rho}\bigl(X_{ij}+U_{ij}\bigr)$$
--   is the unique minimizer over all $Z\in\mathbb R^{n\times n}$ of
--   $$\lambda\|Z\|_1+\frac\rho2\|X-Z+U\|_F^2,$$
--   where $\|Z\|_1=\sum_{i,j}|Z_{ij}|$ and $S_\kappa$ is scalar soft thresholding.
--
--   With $X=X^{k+1}$ and $U=U^k$ this is the Z-update of ADMM for sparse inverse covariance selection.
--
--   **Formalization Note** The regularization weight $\lambda$ is called `lam`. The book takes $\lambda>0$; the statement is made for $\lambda\ge0$, which contains it. The minimization is over all real $n\times n$ matrices; when $X$ and $U$ are symmetric the minimizer is symmetric, so minimizing over symmetric matrices gives the same update.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 47, §6.5 (Z-minimization step); objective on p. 46

import Mathlib
import Definitions.Def_BoydADMM_L1_Basic
import Definitions.Def_BoydADMM_L1_CovSel

open Matrix

namespace BoydADMM.L1

/-- §6.5, p. 47: for `λ ≥ 0` (called `lam`) and `ρ > 0`, the matrix with entries
`S_{λ/ρ}(X_ij + U_ij)` is the unique minimizer of `λ‖Z‖₁ + (ρ/2)‖X − Z + U‖_F²` over all real
`n × n` matrices `Z`. -/
theorem covsel_Z_update {n : ℕ} (lam ρ : ℝ) (hlam : 0 ≤ lam) (hρ : 0 < ρ)
    (X U : Matrix (Fin n) (Fin n) ℝ) :
    IsUniqueMinimizerOn (covselZObjective lam ρ X U) Set.univ
      (Matrix.of fun i j => BoydADMM.Prox.softThreshold (lam / ρ) (X i j + U i j)) := by sorry

end BoydADMM.L1
