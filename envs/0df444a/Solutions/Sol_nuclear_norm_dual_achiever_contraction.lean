-- Prove2me | solution 1 for nuclear_norm_dual_achiever_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T22:06:54.181413+00:00
-- url     : https://prove2.me/submissions/d6b2a3c8-a219-4441-8c65-74873ed60a23

import Theorems.Thm_matrix_svd_exists
import Theorems.Thm_sign_matrix_inner_eq_nuclear_norm
import Theorems.Thm_sign_matrix_spectral_norm_le_one
import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_svd

open MatrixCompletion

theorem solution {n₁ n₂ : ℕ} (N : Matrix (Fin n₁) (Fin n₂) ℝ) :
    ∃ Z : Matrix (Fin n₁) (Fin n₂) ℝ,
      spectralNorm Z ≤ 1 ∧ matrixInner Z N = nuclearNorm N := by
  obtain ⟨r, S, _⟩ := matrix_svd_exists N
  exact ⟨signMatrix S, sign_matrix_spectral_norm_le_one S, sign_matrix_inner_eq_nuclear_norm S⟩
