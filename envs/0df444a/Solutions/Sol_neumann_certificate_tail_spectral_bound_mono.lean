-- Prove2me | solution 1 for neumann_certificate_tail_spectral_bound_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-15T15:18:49.79263+00:00
-- url     : https://prove2.me/submissions/18999a7d-f91f-42d5-aaa9-22d8801cfad0

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion


open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (p : ℝ) (k0 : ℕ) (small large : ℝ) :
    small ≤ large →
    NeumannCertificateTailSpectralBound Omega S p k0 small →
    NeumannCertificateTailSpectralBound Omega S p k0 large := by
  intro hle hsmall K hK
  exact le_trans (hsmall K hK) hle
