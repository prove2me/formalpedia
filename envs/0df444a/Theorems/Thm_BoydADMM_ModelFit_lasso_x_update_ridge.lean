-- Prove2me | Theorems.Thm_BoydADMM_ModelFit_lasso_x_update_ridge
-- name    : BoydADMM.ModelFit.lasso_x_update_ridge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:36:06.251981+00:00
-- url     : https://prove2.me/theorems/e112e40e-cc01-43f7-9ddf-fb8854254111
-- title:
--   §8.2.1, p. 65 — the distributed-lasso xᵢ-update is ridge regression, xᵢ = (AᵢᵀAᵢ + ρI)⁻¹(Aᵢᵀbᵢ + ρ(z − uᵢ))
-- statement:
--   In distributed lasso by splitting across examples, processor $i$ holds a block $A_i\in\mathbb R^{m_i\times n}$ of the feature matrix and the matching block $b_i\in\mathbb R^{m_i}$ of the response, and its $x_i$-update minimizes a Tikhonov-regularized least-squares objective. Let $\rho>0$, $z,u_i\in\mathbb R^n$ (the current consensus variable $z^k$ and scaled dual variable $u_i^k$). Then a point $x\in\mathbb R^n$ minimizes
--   $$\frac12\|A_ix-b_i\|_2^2+\frac{\rho}{2}\|x-z+u_i\|_2^2$$
--   over $\mathbb R^n$ if and only if
--   $$x=(A_i^TA_i+\rho I)^{-1}\bigl(A_i^Tb_i+\rho(z-u_i)\bigr).$$
--   In particular this point is the unique minimizer.
--
--   This is the analytical solution the book gives for each local update of the distributed lasso, the step that runs in parallel over the data blocks.
--
--   **Formalization Note** The book writes "$x_i^{k+1}:=\operatorname{argmin}$ … with analytical solution …"; the statement is the equivalence "minimizer $\iff$ formula", which gives existence and uniqueness of the minimizer together. The iteration indices are dropped: $z=z^k$, $u_i=u_i^k$.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 65, §8.2.1

import Mathlib
import Definitions.Def_BoydADMM_ModelFit_Basic

open Matrix

namespace BoydADMM.ModelFit

/-- §8.2.1, p. 65: the distributed-lasso `xᵢ`-update is a ridge regression with the unique
solution `xᵢ = (AᵢᵀAᵢ + ρI)⁻¹(Aᵢᵀbᵢ + ρ(z − uᵢ))`. -/
theorem lasso_x_update_ridge {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (z u : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (hρ : 0 < ρ)
    (x : EuclideanSpace ℝ (Fin n)) :
    IsMinOn (fun x' : EuclideanSpace ℝ (Fin n) =>
        1 / 2 * ‖Matrix.toEuclideanLin A x' - b‖ ^ 2 + ρ / 2 * ‖x' - z + u‖ ^ 2) Set.univ x ↔
      x = Matrix.toEuclideanLin ((Aᵀ * A + ρ • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹)
        (Matrix.toEuclideanLin Aᵀ b + ρ • (z - u)) := by sorry

end BoydADMM.ModelFit
