-- Prove2me | Theorems.Thm_BoydADMM_ModelFit_group_lasso_eigen_norm
-- name    : BoydADMM.ModelFit.group_lasso_eigen_norm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:37:53.59311+00:00
-- url     : https://prove2.me/theorems/7ffec365-f8bc-44d5-9a4b-0c9a3aaa885a
-- title:
--   §8.3.2, p. 70 — with AᵢᵀAᵢ = Q diag(λ) Qᵀ, ‖(AᵢᵀAᵢ + νI)⁻¹Aᵢᵀv‖₂ = ‖diag(λ + ν1)⁻¹QᵀAᵢᵀv‖₂
-- statement:
--   Let $A_i\in\mathbb R^{m\times n_i}$ and $v\in\mathbb R^m$, and suppose
--   $$A_i^TA_i=Q\,\mathbf{diag}(\mu)\,Q^T$$
--   with $Q\in\mathbb R^{n_i\times n_i}$ orthogonal and $\mu\in\mathbb R^{n_i}$ (so $\mu$ is the vector of eigenvalues of $A_i^TA_i$, the squares of the singular values of $A_i$). Then for every $\nu>0$
--   $$\bigl\|(A_i^TA_i+\nu I)^{-1}A_i^Tv\bigr\|_2=\bigl\|\mathbf{diag}(\mu+\nu\mathbf 1)^{-1}Q^TA_i^Tv\bigr\|_2 .$$
--
--   Once $Q^TA_i^Tv$ is cached, the right-hand side costs $O(n_i)$ flops, which makes the one-parameter search over $\nu$ in the group-lasso update cheap.
--
--   **Formalization Note** The book calls the eigenvalue vector $\lambda$, clashing with the regularization weight; here it is $\mu$. The book assumes $A_i$ tall ($m\ge n_i$) for the cost count; the identity does not need it, and no such hypothesis is imposed. That $\mu$ consists of eigenvalues, and that they are nonnegative, follows from the decomposition, so it is not assumed separately.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 70, §8.3.2

import Mathlib
import Definitions.Def_BoydADMM_ModelFit_Basic

open Matrix

namespace BoydADMM.ModelFit

/-- §8.3.2, p. 70: if `AᵢᵀAᵢ = Q diag(μ) Qᵀ` with `Q` orthogonal, then for `ν > 0`
`‖(AᵢᵀAᵢ + νI)⁻¹Aᵢᵀv‖₂ = ‖diag(μ + ν1)⁻¹ Qᵀ Aᵢᵀ v‖₂`. (The book's eigenvalue vector `λ` is `μ`.) -/
theorem group_lasso_eigen_norm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin n) ℝ) (μ : Fin n → ℝ)
    (hdecomp : Aᵀ * A = Q * Matrix.diagonal μ * Qᵀ) (ν : ℝ) (hν : 0 < ν) :
    ‖ridgeSol A ν v‖ =
      ‖Matrix.toEuclideanLin ((Matrix.diagonal (fun j => μ j + ν))⁻¹ * Qᵀ * Aᵀ) v‖ := by sorry

end BoydADMM.ModelFit
