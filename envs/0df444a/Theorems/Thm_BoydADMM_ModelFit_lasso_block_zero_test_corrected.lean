-- Prove2me | Theorems.Thm_BoydADMM_ModelFit_lasso_block_zero_test_corrected
-- name    : BoydADMM.ModelFit.lasso_block_zero_test_corrected
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:37:03.754986+00:00
-- url     : https://prove2.me/theorems/f8a96e62-457c-42ac-9e37-7c6cb668a36a
-- title:
--   §8.3.1, p. 69 (corrected) — the lasso block update is 0 iff ‖Aᵢᵀv‖_∞ ≤ λ/ρ
-- statement:
--   Let $A_i\in\mathbb R^{m\times n_i}$, $v\in\mathbb R^m$, $\rho>0$ and $\lambda>0$. In the feature-split lasso the $x_i$-update minimizes $\frac{\rho}{2}\|A_ix-v\|_2^2+\lambda\|x\|_1$ with $v=A_ix_i^k+\bar z^k-\overline{Ax}^k-u^k$. Then $x=0$ is a minimizer of
--   $$\frac{\rho}{2}\|A_ix-v\|_2^2+\lambda\|x\|_1$$
--   over $\mathbb R^{n_i}$ if and only if
--   $$\|A_i^Tv\|_\infty=\max_j\bigl|(A_i^Tv)_j\bigr|\le\lambda/\rho .$$
--
--   The test lets a serial implementation skip the blocks whose features are not used.
--
--   **Corrected statement.** The book prints the test with the Euclidean norm, $\|A_i^T(A_ix_i^k+\bar z^k-\overline{Ax}^k-u^k)\|_2\le\lambda/\rho$. That is the test for the group-lasso term $\lambda\|x_i\|_2$ of §8.3.2, and it is false for the $\ell_1$ term: with $A_i=I_2$, $\rho=\lambda=1$ and $v=(0.9,0.9)$ the minimizer is $x_i=0$ although $\|v\|_2\approx1.27>1$. The correct test, stated here, uses $\|\cdot\|_\infty$, the dual norm of $\|\cdot\|_1$.
--
--   **Formalization Note** "$x_i^{k+1}=0$" is read as "$0$ is a minimizer"; uniqueness of the minimizer is not claimed (the objective need not be strictly convex). $\lambda$ is `lam` in Lean.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 69, §8.3.1 (printed with ‖·‖₂; corrected to ‖·‖_∞)

import Mathlib
import Definitions.Def_BoydADMM_ModelFit_Basic

open Matrix

namespace BoydADMM.ModelFit

/-- §8.3.1, p. 69, corrected: `0` minimizes `(ρ/2)‖Aᵢxᵢ − v‖₂² + λ‖xᵢ‖₁` iff
`‖Aᵢᵀv‖_∞ ≤ λ/ρ` (the book prints `‖·‖₂`, which is false for the ℓ1 block term). -/
theorem lasso_block_zero_test_corrected {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) (ρ lam : ℝ) (hρ : 0 < ρ) (hlam : 0 < lam) :
    IsMinOn (fun x : EuclideanSpace ℝ (Fin n) =>
        ρ / 2 * ‖Matrix.toEuclideanLin A x - v‖ ^ 2 + lam * l1norm x) Set.univ 0 ↔
      ∀ j, |Matrix.toEuclideanLin Aᵀ v j| ≤ lam / ρ := by sorry

end BoydADMM.ModelFit
