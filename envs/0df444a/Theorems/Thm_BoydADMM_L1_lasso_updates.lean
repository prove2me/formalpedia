-- Prove2me | Theorems.Thm_BoydADMM_L1_lasso_updates
-- name    : BoydADMM.L1.lasso_updates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:05:30.418989+00:00
-- url     : https://prove2.me/theorems/63895f5b-5662-4f38-b115-06913351101e
-- title:
--   §6.4, p. 43 — lasso ADMM: $x^{k+1}=(A^TA+\rho I)^{-1}(A^Tb+\rho(z^k-u^k))$, $z^{k+1}=S_{\lambda/\rho}(x^{k+1}+u^k)$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $\lambda\ge0$, $\rho>0$ and $z,u\in\mathbb R^n$.
--
--   1. The vector $x^\star=(A^TA+\rho I)^{-1}\bigl(A^Tb+\rho(z-u)\bigr)$ is the unique minimizer over $x\in\mathbb R^n$ of
--   $$\frac12\|Ax-b\|_2^2+\frac\rho2\|x-z+u\|_2^2 .$$
--   2. For every $x\in\mathbb R^n$, the vector with components $S_{\lambda/\rho}(x_i+u_i)$ is the unique minimizer over $z'\in\mathbb R^n$ of
--   $$\lambda\|z'\|_1+\frac\rho2\|x-z'+u\|_2^2 .$$
--
--   With $z=z^k$, $u=u^k$ and $x=x^{k+1}$ these are the x- and z-updates of scaled-form ADMM for the lasso, minimize $(1/2)\|Ax-b\|_2^2+\lambda\|x\|_1$, split as $f(x)+g(z)$ with $x-z=0$. The x-update is a ridge regression; $A^TA+\rho I$ is always invertible because $\rho>0$.
--
--   **Formalization Note** The regularization weight $\lambda$ is called `lam`. The book takes $\lambda>0$; the statement is made for $\lambda\ge0$, which contains it. Part 2 holds for every $x$, in particular for $x=x^{k+1}$. $\|\cdot\|_1$ is the referenced platform definition `HighDimStat.SparseLinear.l1Norm`, $\sum_i|x_i|$.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 43, §6.4

import Mathlib
import Definitions.Def_BoydADMM_L1_Basic
import Definitions.Def_HighDimStat_SparseLinear_L1Norm

open Matrix

namespace BoydADMM.L1

/-- §6.4, p. 43: for `ρ > 0` and `λ ≥ 0` (called `lam`),
(1) `(AᵀA + ρI)⁻¹(Aᵀb + ρ(z − u))` is the unique minimizer of
`(1/2)‖Ax − b‖₂² + (ρ/2)‖x − z + u‖₂²` over `x`, and
(2) for every `x`, the vector with components `S_{λ/ρ}(x_i + u_i)` is the unique minimizer of
`λ‖z'‖₁ + (ρ/2)‖x − z' + u‖₂²` over `z'`. -/
theorem lasso_updates {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (lam ρ : ℝ) (hlam : 0 ≤ lam) (hρ : 0 < ρ) (z u : EuclideanSpace ℝ (Fin n)) :
    IsUniqueMinimizerOn
        (fun x : EuclideanSpace ℝ (Fin n) =>
          (1 / 2) * ‖Matrix.toEuclideanLin A x - b‖ ^ 2 + (ρ / 2) * ‖x - z + u‖ ^ 2) Set.univ
        (Matrix.toEuclideanLin (Aᵀ * A + ρ • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹
          (Matrix.toEuclideanLin Aᵀ b + ρ • (z - u))) ∧
      ∀ x : EuclideanSpace ℝ (Fin n),
        IsUniqueMinimizerOn
          (fun z' : EuclideanSpace ℝ (Fin n) =>
            lam * HighDimStat.SparseLinear.l1Norm (WithLp.ofLp z') +
              (ρ / 2) * ‖x - z' + u‖ ^ 2) Set.univ
          (WithLp.toLp 2 fun i => BoydADMM.Prox.softThreshold (lam / ρ) (x i + u i)) := by sorry

end BoydADMM.L1
