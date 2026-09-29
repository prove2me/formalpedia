-- Prove2me | solution 1 for strict_dual_certificate_normal_component_nonzero_gives_nuclear_norm_gap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T00:49:44.194201+00:00
-- url     : https://prove2.me/submissions/18322c57-c73a-4934-93c9-2eafc1b3683f

import Mathlib.Tactic
import Theorems.Thm_nuclear_norm_lower_bound_by_tangent_sign_and_normal_norm
import Theorems.Thm_strict_dual_certificate_inner_tangent_eq_neg_normal_of_feasible_perturbation
import Theorems.Thm_normal_certificate_inner_lt_nuclear_norm_of_nonzero_normal_component
import Definitions.Def_matrix_completion_tangent

open MatrixCompletion


open MatrixCompletion

/-- Prove the normal-component case of Lemma 3.1 from the nuclear-norm
subgradient lower bound, the feasible-perturbation certificate identity, and
strict nuclear/spectral duality on the normal space. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (Y H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    StrictDualCertificate Omega S Y →
    samplingProjection Omega H = 0 →
    normalProjection S H ≠ 0 →
    nuclearNorm M < nuclearNorm (M + H) := by
  intro hCertificate hSample hNormalNonzero
  have hNormalSmall := hCertificate.2.2
  have hLower := nuclear_norm_lower_bound_by_tangent_sign_and_normal_norm S H
  have hInner :=
    strict_dual_certificate_inner_tangent_eq_neg_normal_of_feasible_perturbation
      S Omega Y H hCertificate hSample
  have hStrict :=
    normal_certificate_inner_lt_nuclear_norm_of_nonzero_normal_component
      S Y H hNormalSmall hNormalNonzero
  have hAlgebra :
      nuclearNorm M <
        nuclearNorm M +
            matrixInner (signMatrix S) (tangentProjection S H) +
              nuclearNorm (normalProjection S H) := by
    rw [hInner]
    linarith
  exact lt_of_lt_of_le hAlgebra hLower
