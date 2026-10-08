-- Prove2me | Theorems.Thm_BoydADMM_Nonconvex_factor_model_X_update
-- name    : BoydADMM.Nonconvex.factor_model_X_update
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:19:55.410978+00:00
-- url     : https://prove2.me/theorems/cfe30e95-ed47-437e-8c0f-dc133e489d14
-- title:
--   §9.1.2 — the factor-model ADMM X-update is the unique minimizer
-- statement:
--   Let $n\ge1$, let $\Sigma,Z,U\in\mathbb R^{n\times n}$ be symmetric, and let $\rho>0$. Define $f_\Sigma(X)=\inf_{d\ge0}\frac12\|X+\operatorname{diag}(d)-\Sigma\|_F^2$. The matrix $X^+$ has entries
--
--   $$X^+_{ij}=\frac{\Sigma_{ij}+\rho(Z_{ij}-U_{ij})}{1+\rho}\quad(i\ne j),$$
--
--   $$X^+_{ii}=\begin{cases}\frac{\Sigma_{ii}+\rho(Z_{ii}-U_{ii})}{1+\rho},&\Sigma_{ii}\le Z_{ii}-U_{ii},\\ Z_{ii}-U_{ii},&\Sigma_{ii}>Z_{ii}-U_{ii}.\end{cases}$$
--
--   Then $X^+$ is symmetric and is the unique minimizer, among symmetric matrices $X$, of
--
--   $$f_\Sigma(X)+\frac\rho2\|X-Z+U\|_F^2.$$
--
--   This gives the exact X-step of the factor-model ADMM iteration; the positive semidefinite rank constraint belongs to the separate Z-step.
--
--   **Formalization Note** The book's branch conditions print $Z_{ii}-U_{ii}$ without iteration superscripts, although the surrounding update uses $Z^k,U^k$; this statement uses the current $Z,U$. The book takes a positive penalty and positive matrix dimension, both explicit here. The unique-minimizer clause states more than stationarity and includes symmetry of the candidate.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 75, §9.1.2, X-update display

import Mathlib
import Definitions.Def_BoydADMM_Nonconvex_FactorModel

namespace BoydADMM.Nonconvex

/-- §9.1.2, p. 75: the printed entrywise formula, with the omitted iteration
superscripts restored, is the unique symmetric minimizer of the `X`-update. -/
theorem factor_model_X_update {n : ℕ} (Sigma Z U : SqMat n) (rho : ℝ)
    (hn : 0 < n) (hSigma : IsSymmetric Sigma) (hZ : IsSymmetric Z) (hU : IsSymmetric U)
    (hrho : 0 < rho) :
    IsSymmetric (xUpdate Sigma Z U rho) ∧
    (∀ X : SqMat n, IsSymmetric X →
      xSubproblem Sigma Z U rho (xUpdate Sigma Z U rho) ≤
        xSubproblem Sigma Z U rho X ∧
      (xSubproblem Sigma Z U rho X =
        xSubproblem Sigma Z U rho (xUpdate Sigma Z U rho) →
        X = xUpdate Sigma Z U rho)) := by sorry

end BoydADMM.Nonconvex
