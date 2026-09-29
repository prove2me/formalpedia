-- Prove2me | solution 1 for tangent_coordinate_projection_frobenius_sq_le_abs_diagonal_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T05:20:46.561432+00:00
-- url     : https://prove2.me/submissions/a75d3ceb-5540-469c-b958-1ca6c143f0c1

import Theorems.Thm_tangent_coordinate_projection_frobenius_sq_eq_coordinate_kernel_diagonal
import Mathlib.Tactic

open MatrixCompletion

/-!
Source: Candes-Recht 2008, Section 3, PDF p. 15, equation (3.5), and
PDF p. 18, equation (4.8).  Equation (3.5) defines `P_T` as the orthogonal
tangent-space projection.  Equation (4.8) uses the coordinate radius
`||P_T(e_i e_j^T)||_F`; the diagonal kernel is
`<P_T(e_i e_j^T), e_i e_j^T>`.

Reduction: the child theorem proves the substantive orthogonal-projection
identity
`||P_T(e_i e_j^T)||_F^2 = <P_T(e_i e_j^T), e_i e_j^T>`, expressed in Lean as
`frobeniusNormSq = tangentCoordinateKernel`.  The present sketch only unfolds
`frobeniusNorm = sqrt(frobeniusNormSq)` and uses `x <= |x|`.
-/

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
    ∀ i : Fin n₁, ∀ j : Fin n₂,
      frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ^ 2 ≤
        |tangentCoordinateKernel S i j i j| := by
  intro i j
  let X : Matrix (Fin n₁) (Fin n₂) ℝ :=
    tangentProjection S (coordinateMatrix i j)
  have hnormsq_nonneg : 0 ≤ frobeniusNormSq X := by
    unfold frobeniusNormSq
    positivity
  have hnorm :
      frobeniusNorm X ^ 2 = frobeniusNormSq X := by
    simp [frobeniusNorm, Real.sq_sqrt hnormsq_nonneg]
  calc
    frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ^ 2
        = frobeniusNormSq
            (tangentProjection S (coordinateMatrix i j)) := by
          simpa [X] using hnorm
    _ = tangentCoordinateKernel S i j i j :=
        tangent_coordinate_projection_frobenius_sq_eq_coordinate_kernel_diagonal S i j
    _ ≤ |tangentCoordinateKernel S i j i j| := le_abs_self _
