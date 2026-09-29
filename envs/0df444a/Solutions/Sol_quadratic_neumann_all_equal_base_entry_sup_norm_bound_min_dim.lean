-- Prove2me | solution 1 for quadratic_neumann_all_equal_base_entry_sup_norm_bound_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T15:12:18.009454+00:00
-- url     : https://prove2.me/submissions/2e23a9c1-88ac-4a52-99f3-a0b15c882c8e

import Mathlib.Tactic
import Theorems.Thm_entry_sup_norm_quadratic_all_equal_base_bound_from_sign_and_kernel_bounds
import Theorems.Thm_entry_sup_norm_sign_matrix_bound_from_a0_min_dim
import Theorems.Thm_tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim

open MatrixCompletion

/-- Source: Candes-Recht 2008, PDF p. 23, estimates (6.2) and (6.4), together
with PDF p. 30, equation (6.21).  The paper states after (6.2)--(6.4) that the
rectangular case replaces `n` by `min(n₁,n₂)`. -/
theorem solution :
    ∃ Cbase : ℝ, 0 < Cbase ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        entrySupNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
          Cbase * μ₀ ^ 3 *
            (((r : ℝ) / (↑(min n₁ n₂))) ^ 3) := by
  rcases entry_sup_norm_sign_matrix_bound_from_a0_min_dim with
    ⟨Csign, hCsign_pos, hsign⟩
  rcases tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim with
    ⟨Cker, hCker_pos, hker⟩
  refine ⟨Csign * Cker ^ 2, mul_pos hCsign_pos (pow_pos hCker_pos 2), ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0
  let scale : ℝ := (r : ℝ) / (↑(min n₁ n₂))
  let signBound : ℝ := Csign * μ₀ * scale
  let kernelBound : ℝ := Cker * μ₀ * scale
  have hsign_nonneg : 0 ≤ signBound := by
    dsimp [signBound, scale]
    positivity
  have hkernel_nonneg : 0 ≤ kernelBound := by
    dsimp [kernelBound, scale]
    positivity
  have hgeneric :=
    entry_sup_norm_quadratic_all_equal_base_bound_from_sign_and_kernel_bounds
      hn₁ hn₂ S hsign_nonneg hkernel_nonneg
      (hsign n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0)
      (hker n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0)
  calc
    entrySupNorm (quadraticNeumannAllEqualBaseMatrix S)
        ≤ signBound * kernelBound ^ 2 := hgeneric
    _ = (Csign * Cker ^ 2) * μ₀ ^ 3 *
          (((r : ℝ) / (↑(min n₁ n₂))) ^ 3) := by
      dsimp [signBound, kernelBound, scale]
      ring
