-- Prove2me | solution 1 for dual_certificate_with_restricted_sampling_implies_unique_completion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T04:19:45.705096+00:00
-- url     : https://prove2.me/submissions/1c3e6a9c-73b9-47f1-8a1d-ed03e61267c8

import Theorems.Thm_strict_dual_certificate_and_injectivity_force_nuclear_norm_gap

open MatrixCompletion

/-- Finish Lemma 3.1 by unpacking the existential dual certificate and applying
the fixed-certificate nuclear-norm gap theorem. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    SamplingOperatorInjectiveOnT Omega S →
    (∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ, StrictDualCertificate Omega S Y) →
    IsUniqueMinimizer Omega M := by
  intro hInjective hCertificateExists
  rcases hCertificateExists with ⟨Y, hCertificate⟩
  exact strict_dual_certificate_and_injectivity_force_nuclear_norm_gap
    S Omega Y hInjective hCertificate
