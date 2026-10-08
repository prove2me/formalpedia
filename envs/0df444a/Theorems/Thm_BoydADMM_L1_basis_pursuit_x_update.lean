-- Prove2me | Theorems.Thm_BoydADMM_L1_basis_pursuit_x_update
-- name    : BoydADMM.L1.basis_pursuit_x_update
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:05:21.380662+00:00
-- url     : https://prove2.me/theorems/93af033d-28e6-419e-ae2c-0eeb6548fe87
-- title:
--   §6.2, p. 41 — the basis-pursuit x-update is $(I-A^T(AA^T)^{-1}A)(z^k-u^k)+A^T(AA^T)^{-1}b$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ with $AA^T$ invertible, $b\in\mathbb R^m$, and $z,u\in\mathbb R^n$. Then
--   $$x^\star=\bigl(I-A^T(AA^T)^{-1}A\bigr)(z-u)+A^T(AA^T)^{-1}b$$
--   is the Euclidean projection of $z-u$ onto the affine set $\{x\in\mathbb R^n\mid Ax=b\}$: $Ax^\star=b$, and $\|x^\star-(z-u)\|_2<\|x-(z-u)\|_2$ for every other $x$ with $Ax=b$.
--
--   With $z=z^k$ and $u=u^k$ this is the x-update $x^{k+1}=\Pi(z^k-u^k)$ of ADMM for basis pursuit, minimize $\|x\|_1$ subject to $Ax=b$: a minimum Euclidean norm problem with linear constraints, in closed form.
--
--   **Formalization Note** The book assumes $m<n$ and uses $(AA^T)^{-1}$ without stating that it exists; the statement assumes $\det(AA^T)\ne0$ ($A$ has full row rank), which is what the formula needs. Uniqueness of the nearest point is part of the conclusion. Vectors are `EuclideanSpace`, matrices act by `Matrix.toEuclideanLin`.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 41, §6.2

import Mathlib
import Definitions.Def_BoydADMM_L1_Basic

open Matrix

namespace BoydADMM.L1

/-- §6.2, p. 41: if `AAᵀ` is invertible, then
`(I − Aᵀ(AAᵀ)⁻¹A)(z − u) + Aᵀ(AAᵀ)⁻¹b` is the Euclidean projection `Π(z − u)` of `z − u` onto
`{x ∈ ℝⁿ | Ax = b}`: the unique point of that set nearest to `z − u`. -/
theorem basis_pursuit_x_update {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (hA : (A * Aᵀ).det ≠ 0) (z u : EuclideanSpace ℝ (Fin n)) :
    IsUniqueMinimizerOn (fun x : EuclideanSpace ℝ (Fin n) => ‖x - (z - u)‖)
      {x | Matrix.toEuclideanLin A x = b}
      (Matrix.toEuclideanLin (1 - Aᵀ * (A * Aᵀ)⁻¹ * A) (z - u) +
        Matrix.toEuclideanLin (Aᵀ * (A * Aᵀ)⁻¹) b) := by sorry

end BoydADMM.L1
