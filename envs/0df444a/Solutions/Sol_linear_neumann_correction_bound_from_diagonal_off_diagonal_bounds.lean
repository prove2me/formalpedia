-- Prove2me | solution 1 for linear_neumann_correction_bound_from_diagonal_off_diagonal_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T16:09:48.800982+00:00
-- url     : https://prove2.me/submissions/859e38ff-73c4-4ce2-bb6e-ac7635352102

import Theorems.Thm_first_neumann_certificate_term_spectral_norm_le_diagonal_off_diagonal_sum
import Mathlib.Tactic

open MatrixCompletion

private lemma spectralNorm_add_le
    {n₁ n₂ : ℕ} (X Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (X + Y) ≤ spectralNorm X + spectralNorm Y := by
  unfold spectralNorm
  have hlin :
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (X + Y)) =
        LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X) +
          LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Y) := by
    ext v i
    simp [Matrix.toEuclideanLin]
  rw [hlin]
  exact norm_add_le _ _

/--
Source: Candes-Recht 2008, PDF p. 26, the inequality immediately before
equation (6.8), and PDF p. 26, equation (6.8).

The paper does not identify the normal-projected certificate term with the
diagonal/off-diagonal sum.  Instead it first bounds the normal-projected term by
the unprojected centered first correction, then equation (6.8) splits that
unprojected correction into diagonal and off-diagonal pieces.  This sketch uses
the source-correct comparison child and then applies the spectral-norm triangle
inequality.
-/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (p Cdiag Coff lam : ℝ) :
    spectralNorm (linearNeumannDiagonalContribution Omega S p) ≤
      Cdiag * Real.rpow lam (-1) →
    spectralNorm (linearNeumannOffDiagonalContribution Omega S p) ≤
      Coff * Real.rpow lam (-1) →
    NeumannCertificateTermSpectralBound Omega S p 1
      ((Cdiag + Coff) * Real.rpow lam (-1)) := by
  intro hdiag hoff
  unfold NeumannCertificateTermSpectralBound
  calc
    spectralNorm (neumannCertificateTerm Omega S p 1)
        ≤ spectralNorm
            (linearNeumannDiagonalContribution Omega S p +
              linearNeumannOffDiagonalContribution Omega S p) :=
        first_neumann_certificate_term_spectral_norm_le_diagonal_off_diagonal_sum
          S Omega p
    _ ≤ spectralNorm (linearNeumannDiagonalContribution Omega S p) +
          spectralNorm (linearNeumannOffDiagonalContribution Omega S p) :=
        spectralNorm_add_le _ _
    _ ≤ Cdiag * Real.rpow lam (-1) + Coff * Real.rpow lam (-1) :=
        add_le_add hdiag hoff
    _ = (Cdiag + Coff) * Real.rpow lam (-1) := by ring
