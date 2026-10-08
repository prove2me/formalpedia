-- Prove2me | Theorems.Thm_BookProof_ChapterA3_lambdaOf_neg
-- name    : BookProof.ChapterA3.lambdaOf_neg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T12:34:35.018374+00:00
-- url     : https://prove2.me/theorems/9a9b94fd-3bd6-45fe-83f3-ac492e587127
-- title:
--   `BookProof.ChapterA3.lambdaOf_neg` {S : Matrix (Fin 4) (Fin 4) ℝ} (h : IsPin S) : LambdaOf (-S) = LambdaOf S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3c`.
--
--   `BookProof.ChapterA3.lambdaOf_neg` {S : Matrix (Fin 4) (Fin 4) ℝ} (h : IsPin S) : LambdaOf (-S) = LambdaOf S
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.lambdaOf_neg`.

-- Generated from ChapterA3c.lean — theorem BookProof.ChapterA3.lambdaOf_neg
import Mathlib
import Definitions.Def_ChapterA3c
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.lambdaOf_neg {S : Matrix (Fin 4) (Fin 4) ℝ} (h : IsPin S) :
    LambdaOf (-S) = LambdaOf S := by sorry
