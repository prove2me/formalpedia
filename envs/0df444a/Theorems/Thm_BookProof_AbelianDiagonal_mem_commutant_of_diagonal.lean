-- Prove2me | Theorems.Thm_BookProof_AbelianDiagonal_mem_commutant_of_diagonal
-- name    : BookProof.AbelianDiagonal.mem_commutant_of_diagonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:50:22.806155+00:00
-- url     : https://prove2.me/theorems/3cd81253-d67d-4469-b2fe-877440a0ffba
-- title:
--   `BookProof.AbelianDiagonal.mem_commutant_of_diagonal` (e : n → ℂ) (d : n → ℂ) : Matrix.diagonal e * Matrix.diagonal d = Matrix.diagonal d * Matrix.diagonal e
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianDiagonal`.
--
--   `BookProof.AbelianDiagonal.mem_commutant_of_diagonal` (e : n → ℂ) (d : n → ℂ) : Matrix.diagonal e * Matrix.diagonal d = Matrix.diagonal d * Matrix.diagonal e
--
--   Formalization note: Lean 4 identifier `BookProof.AbelianDiagonal.mem_commutant_of_diagonal`.

-- Generated from ChapterAbelianDiagonal.lean — theorem BookProof.AbelianDiagonal.mem_commutant_of_diagonal
import Mathlib
import Definitions.Def_ChapterAbelianDiagonal
open BookProof.AbelianDiagonal



open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.AbelianDiagonal.mem_commutant_of_diagonal (e : n → ℂ) (d : n → ℂ) :
    Matrix.diagonal e * Matrix.diagonal d = Matrix.diagonal d * Matrix.diagonal e := by sorry
