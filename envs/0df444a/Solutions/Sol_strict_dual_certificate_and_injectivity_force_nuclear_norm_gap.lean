-- Prove2me | solution 1 for strict_dual_certificate_and_injectivity_force_nuclear_norm_gap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T00:01:24.310693+00:00
-- url     : https://prove2.me/submissions/c6c5ff11-717d-44cc-bc24-e34d9d7a5c47

import Theorems.Thm_strict_certificate_and_injectivity_increase_nuclear_norm_for_perturbation
import Theorems.Thm_agreement_gives_zero_sampled_perturbation
import Theorems.Thm_distinct_matrix_subtraction_nonzero
import Theorems.Thm_nuclear_norm_gap_transfer_from_subtraction_perturbation
import Definitions.Def_matrix_completion_basic
import Definitions.Def_matrix_completion_tangent

open MatrixCompletion


open MatrixCompletion

/-- Pass from a feasible competing matrix `X` to the perturbation `H = X - M`
and apply the perturbation form of the deterministic certificate lemma. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    SamplingOperatorInjectiveOnT Omega S →
    StrictDualCertificate Omega S Y →
    ∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
      AgreesOn Omega X M → X ≠ M → nuclearNorm M < nuclearNorm X := by
  intro hInjective hCertificate X hAgree hDistinct
  have hSample := agreement_gives_zero_sampled_perturbation Omega X M hAgree
  have hNonzero := distinct_matrix_subtraction_nonzero X M hDistinct
  have hPerturbationGap :=
    strict_certificate_and_injectivity_increase_nuclear_norm_for_perturbation
      S Omega Y (X - M) hInjective hCertificate hSample hNonzero
  exact nuclear_norm_gap_transfer_from_subtraction_perturbation X M hPerturbationGap
