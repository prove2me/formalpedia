-- Prove2me | solution 1 for tangent_coordinate_frobenius_bound_from_a0_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T04:57:42.725074+00:00
-- url     : https://prove2.me/submissions/4c9669b4-bdf0-44fd-8c3e-ce03721e2aa7

import Theorems.Thm_tangent_coordinate_projection_frobenius_sq_le_abs_diagonal_kernel
import Theorems.Thm_tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim

open MatrixCompletion

/--
Source: Candes-Recht 2008, PDF p. 18 equation (4.8), PDF p. 23 estimate
(6.2), and the rectangular-scale convention after PDF p. 24 equations
(6.2)--(6.4).

The reduction turns the A0 diagonal-kernel estimate into the Frobenius
coordinate-radius estimate used by Rudelson's selection theorem.  The geometric
child identifies the squared Frobenius norm of `P_T(e_i e_j^T)` with the
corresponding diagonal tangent kernel up to absolute value; the already-proved
A0 child bounds that kernel by `O(μ₀ r / min(n₁,n₂))`.
-/
theorem solution :
    ∃ Ccoord : ℝ, 0 < Ccoord ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        TangentCoordinateFrobeniusBound S
          (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  rcases tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim with
    ⟨Cker, hCker, hKernel⟩
  refine ⟨Cker, hCker, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 i j
  have hFrob :=
    tangent_coordinate_projection_frobenius_sq_le_abs_diagonal_kernel S i j
  have hKer :=
    hKernel n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 i j
  refine le_trans hFrob (le_of_le_of_eq hKer ?_)
  ring
