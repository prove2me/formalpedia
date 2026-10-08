-- Prove2me | Theorems.Thm_BookProof_ChapterA3_lambda_two_to_one
-- name    : BookProof.ChapterA3.lambda_two_to_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T12:36:51.823131+00:00
-- url     : https://prove2.me/theorems/0d19e3c6-90ab-416a-84b3-3ecbdce5786c
-- title:
--   `BookProof.ChapterA3.lambda_two_to_one` (hpf : PauliFundamental) {S S' : Matrix (Fin 4) (Fin 4) ℝ} (hS : IsPin S) (hS' : IsPin S') (h : LambdaOf S = LambdaOf S') : S' = S ∨ S' = -S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3c`.
--
--   `BookProof.ChapterA3.lambda_two_to_one` (hpf : PauliFundamental) {S S' : Matrix (Fin 4) (Fin 4) ℝ} (hS : IsPin S) (hS' : IsPin S') (h : LambdaOf S = LambdaOf S') : S' = S ∨ S' = -S
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.lambda_two_to_one`.

-- Generated from ChapterA3c.lean — theorem BookProof.ChapterA3.lambda_two_to_one
import Mathlib
import Definitions.Def_ChapterA3c
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.lambda_two_to_one (hpf : PauliFundamental)
    {S S' : Matrix (Fin 4) (Fin 4) ℝ} (hS : IsPin S) (hS' : IsPin S')
    (h : LambdaOf S = LambdaOf S') : S' = S ∨ S' = -S := by sorry
