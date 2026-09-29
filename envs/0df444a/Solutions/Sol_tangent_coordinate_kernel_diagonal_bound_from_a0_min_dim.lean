-- Prove2me | solution 1 for tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T17:06:04.787989+00:00
-- url     : https://prove2.me/submissions/2c080235-8f92-4443-97fc-a123dbba4860

import Mathlib.Tactic
import Theorems.Thm_a0_singular_coordinate_energy_bounds
import Theorems.Thm_svd_singular_coordinate_energy_le_one
import Theorems.Thm_tangent_coordinate_kernel_diagonal_bound_from_singular_coordinate_energies

open MatrixCompletion

open scoped Classical BigOperators

/--
Source: Candes-Recht 2008, PDF p. 23, estimate (6.2), together with the
rectangular-scale convention stated after PDF p. 24, estimates (6.2)--(6.4).

Estimate (6.2) bounds the diagonal tangent-coordinate kernel by the incoherence
scale.  The reduction separates the finite-dimensional proof into three parts:
A0 gives coordinate-energy bounds for the left and right singular-vector
families, orthonormality gives the Bessel bounds that each such coordinate
energy is at most one, and the remaining child converts those energy estimates
into the diagonal tangent-kernel bound at scale `μ₀ r / min(n₁,n₂)`.
-/
theorem solution :
    ∃ Cker : ℝ, 0 < Cker ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ i j,
          |tangentCoordinateKernel S i j i j| ≤
            Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
  rcases tangent_coordinate_kernel_diagonal_bound_from_singular_coordinate_energies with
    ⟨Cker, hCker_pos, hker⟩
  refine ⟨Cker, hCker_pos, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 i j
  have hEnergy :=
    a0_singular_coordinate_energy_bounds S μ₀ hn₁ hn₂ hr hA0
  have hOne := svd_singular_coordinate_energy_le_one S
  exact hker n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀
    hEnergy.1 hEnergy.2 hOne.1 hOne.2 i j
