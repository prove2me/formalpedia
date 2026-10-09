-- Prove2me | Theorems.Thm_BookProof_ChapterE3_euler_density_matrix
-- name    : BookProof.ChapterE3.euler_density_matrix
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:12:32.463328+00:00
-- url     : https://prove2.me/theorems/e0bc628c-ac23-4dc2-a90f-1063c5cc67bd
-- title:
--   `BookProof.ChapterE3.euler_density_matrix` (l w : Fin n → ℝ) (θ : ℝ) : Matrix.vecMulVec (fun i => Real.cos θ * l i + Real.sin θ * w i) (fun i => Real.cos θ * l i + Real.sin θ * w i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE3`.
--
--   `BookProof.ChapterE3.euler_density_matrix` (l w : Fin n → ℝ) (θ : ℝ) : Matrix.vecMulVec (fun i => Real.cos θ * l i + Real.sin θ * w i) (fun i => Real.cos θ * l i + Real.sin θ * w i) = (1 / 2 : ℝ) • (Matrix.vecMulVec l l + Matrix.vecMulVec w w) + (Real.cos (2 * θ) / 2) • (Matrix.vecMulVec l l - Matrix.vecMulVec w w) + (Real.sin (2 * θ) / 2) • (Matrix.vecMulVec l w + Matrix.vecMulVec w l)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE3.euler_density_matrix`.

-- Generated from ChapterE3.lean — theorem BookProof.ChapterE3.euler_density_matrix
import Mathlib
import Definitions.Def_ChapterE3
open BookProof.ChapterE3


open scoped Matrix BigOperators


variable {n : ℕ}

theorem BookProof.ChapterE3.euler_density_matrix (l w : Fin n → ℝ) (θ : ℝ) :
    Matrix.vecMulVec (fun i => Real.cos θ * l i + Real.sin θ * w i)
        (fun i => Real.cos θ * l i + Real.sin θ * w i)
      = (1 / 2 : ℝ) • (Matrix.vecMulVec l l + Matrix.vecMulVec w w)
        + (Real.cos (2 * θ) / 2) • (Matrix.vecMulVec l l - Matrix.vecMulVec w w)
        + (Real.sin (2 * θ) / 2) • (Matrix.vecMulVec l w + Matrix.vecMulVec w l) := by sorry
