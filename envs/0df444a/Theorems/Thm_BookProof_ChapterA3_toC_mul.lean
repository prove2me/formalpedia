-- Prove2me | Theorems.Thm_BookProof_ChapterA3_toC_mul
-- name    : BookProof.ChapterA3.toC_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T12:02:50.504592+00:00
-- url     : https://prove2.me/theorems/2d9b366a-e2cb-4bb1-8208-716eed14090b
-- title:
--   `BookProof.ChapterA3.toC_mul` (M N : Matrix (Fin 4) (Fin 4) ℝ) : toC (M * N) = toC M * toC N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3b`.
--
--   `BookProof.ChapterA3.toC_mul` (M N : Matrix (Fin 4) (Fin 4) ℝ) : toC (M * N) = toC M * toC N
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.toC_mul`.

-- Generated from ChapterA3b.lean — theorem BookProof.ChapterA3.toC_mul
import Mathlib
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.toC_mul (M N : Matrix (Fin 4) (Fin 4) ℝ) : toC (M * N) = toC M * toC N := by sorry
