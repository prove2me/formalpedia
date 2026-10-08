-- Prove2me | Theorems.Thm_BookProof_ChapterA3_hasLambda_LambdaOf
-- name    : BookProof.ChapterA3.hasLambda_LambdaOf
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T12:20:27.58697+00:00
-- url     : https://prove2.me/theorems/664c1e8a-c396-426d-8af5-04006d18d4d2
-- title:
--   `BookProof.ChapterA3.hasLambda_LambdaOf` (S : Matrix (Fin 4) (Fin 4) ℝ) (h : ∃ Λ, HasLambda S Λ) : HasLambda S (LambdaOf S)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3c`.
--
--   `BookProof.ChapterA3.hasLambda_LambdaOf` (S : Matrix (Fin 4) (Fin 4) ℝ) (h : ∃ Λ, HasLambda S Λ) : HasLambda S (LambdaOf S)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.hasLambda_LambdaOf`.

-- Generated from ChapterA3c.lean — theorem BookProof.ChapterA3.hasLambda_LambdaOf
import Mathlib
import Definitions.Def_ChapterA3c
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.hasLambda_LambdaOf (S : Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∃ Λ, HasLambda S Λ) : HasLambda S (LambdaOf S) := by sorry
