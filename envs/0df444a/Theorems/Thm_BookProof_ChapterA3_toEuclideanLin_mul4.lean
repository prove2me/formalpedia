-- Prove2me | Theorems.Thm_BookProof_ChapterA3_toEuclideanLin_mul4
-- name    : BookProof.ChapterA3.toEuclideanLin_mul4
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:27:38.397802+00:00
-- url     : https://prove2.me/theorems/687f2075-0265-4aa6-8af7-3a186a7a87fc
-- title:
--   `BookProof.ChapterA3.toEuclideanLin_mul4` (A B : Matrix (Fin 4) (Fin 4) ℂ) : Matrix.toEuclideanLin (A * B) = (Matrix.toEuclideanLin A) ∘ₗ (Matrix.toEuclideanLin B)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliCommutant`.
--
--   `BookProof.ChapterA3.toEuclideanLin_mul4` (A B : Matrix (Fin 4) (Fin 4) ℂ) : Matrix.toEuclideanLin (A * B) = (Matrix.toEuclideanLin A) ∘ₗ (Matrix.toEuclideanLin B)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.toEuclideanLin_mul4`.

-- Generated from ChapterPauliCommutant.lean — theorem BookProof.ChapterA3.toEuclideanLin_mul4
import Mathlib
import Definitions.Def_ChapterPauliCommutant
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.toEuclideanLin_mul4 (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix.toEuclideanLin (A * B)
      = (Matrix.toEuclideanLin A) ∘ₗ (Matrix.toEuclideanLin B) := by sorry
