-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_fin_matrix_last_row_split
-- name    : AppliedSDE.SarkkaSolin.fin_matrix_last_row_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:45:15.500842+00:00
-- url     : https://prove2.me/theorems/519cdbb2-b782-45ad-84f4-866b1a68a672
-- title:
--   Last coordinate of a finite matrix-vector product as prefix dot product plus final term
-- statement:
--   Splits the last coordinate of a finite matrix-vector product into the dot product of its prefix row with the prefix vector, plus the last diagonal entry times the final coordinate. This is the matrix row decomposition needed to apply block Schur complement Kalman identities to the AR1 noisy covariance matrix.
-- source:
--   Sarkka and Solin (2019), Gaussian-process/Kalman batch-sequential equivalence, finite covariance decomposition; Mathlib Fin.sum_univ_castSucc.

import Mathlib
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.fin_matrix_last_row_split
    (n : ℕ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    (z : Fin (n + 2) -> ℝ) :
    (K.mulVec z) (Fin.last (n + 1)) =
      (fun i : Fin (n + 1) => K (Fin.last (n + 1)) i.castSucc)
        ⬝ᵥ (fun i => z i.castSucc) +
      K (Fin.last (n + 1)) (Fin.last (n + 1)) *
        z (Fin.last (n + 1)) := by
  sorry
