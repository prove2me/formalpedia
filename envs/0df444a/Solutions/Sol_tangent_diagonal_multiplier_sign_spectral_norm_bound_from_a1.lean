-- Prove2me | solution 1 for tangent_diagonal_multiplier_sign_spectral_norm_bound_from_a1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-23T16:41:02.916959+00:00
-- url     : https://prove2.me/submissions/9e53507a-8958-40ee-a33a-d8c7f49ea744

import Theorems.Thm_sign_matrix_coordinate_energy_bounds_from_a1
import Theorems.Thm_svd_singular_coordinate_energy_le_one
import Theorems.Thm_tangent_diagonal_multiplier_spectral_norm_bound_from_singular_coordinate_energies
import Mathlib.Tactic

open MatrixCompletion

/-!
Source: Candes-Recht 2008, PDF p. 4, assumption A1, and PDF p. 27,
Lemma 6.4 equations (6.10)--(6.11).  A1 bounds entries of
`E = U Vᵀ`; row and column `ℓ₂` identities for `U Vᵀ` convert this into
coordinate-energy bounds at scale `μ₁²`.  Lemma 6.4 then gives the diagonal
tangent-kernel multiplier estimate with `μ₁² r / min(n₁,n₂)`.
-/

theorem solution :
    ∃ Cdiag : ℝ, 0 < Cdiag ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₁ → A1 S μ₁ →
        spectralNorm (tangentDiagonalMultiplier S (signMatrix S)) ≤
          Cdiag * (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂))) *
            spectralNorm (signMatrix S) := by
  rcases tangent_diagonal_multiplier_spectral_norm_bound_from_singular_coordinate_energies with
    ⟨Cdiag, hCdiag, hCore⟩
  refine ⟨Cdiag, hCdiag, ?_⟩
  intro n₁ n₂ r M μ₁ S hn₁ hn₂ hr hμ₁ hA1
  have hμsq : 1 ≤ μ₁ ^ 2 := by
    nlinarith [sq_nonneg (μ₁ - 1)]
  rcases sign_matrix_coordinate_energy_bounds_from_a1
      n₁ n₂ r M μ₁ S hn₁ hn₂ hr hμ₁ hA1 with
    ⟨hu, hv⟩
  rcases svd_singular_coordinate_energy_le_one S with
    ⟨huOne, hvOne⟩
  exact hCore n₁ n₂ r M (μ₁ ^ 2) S (signMatrix S)
    hn₁ hn₂ hr hμsq hu hv huOne hvOne
