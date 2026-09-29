-- Prove2me | solution 1 for neumann_certificate_term_spectral_bound_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-15T15:18:49.439555+00:00
-- url     : https://prove2.me/submissions/9b1547fd-3a26-43de-83b9-0520e4772c88

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion


open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (p : ℝ) (k : ℕ) (small large : ℝ) :
    small ≤ large →
    NeumannCertificateTermSpectralBound Omega S p k small →
    NeumannCertificateTermSpectralBound Omega S p k large := by
  intro hle hsmall
  exact le_trans hsmall hle
