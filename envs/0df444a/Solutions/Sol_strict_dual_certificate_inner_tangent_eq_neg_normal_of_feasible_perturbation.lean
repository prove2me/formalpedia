-- Prove2me | solution 1 for strict_dual_certificate_inner_tangent_eq_neg_normal_of_feasible_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T01:29:12.303024+00:00
-- url     : https://prove2.me/submissions/577d3948-e16a-43f5-b43d-23c6830d78f8

import Mathlib.Tactic
import Theorems.Thm_supported_matrix_inner_zero_of_zero_sampling_projection
import Theorems.Thm_matrix_inner_tangent_normal_decomposition_of_certificate
import Definitions.Def_matrix_completion_tangent

open MatrixCompletion


open MatrixCompletion

/-- Split the certificate inner product into tangent and normal pieces, and use
support on `Omega` plus feasibility of the perturbation to make the total inner
product vanish. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (Y H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    StrictDualCertificate Omega S Y →
    samplingProjection Omega H = 0 →
    matrixInner (signMatrix S) (tangentProjection S H) =
      -matrixInner (normalProjection S Y) (normalProjection S H) := by
  intro hCertificate hSample
  rcases hCertificate with ⟨hSupport, hTangent, _hNormalSmall⟩
  have hZero :=
    supported_matrix_inner_zero_of_zero_sampling_projection Omega Y H
      hSupport hSample
  have hSplit :=
    matrix_inner_tangent_normal_decomposition_of_certificate S Y H hTangent
  linarith
