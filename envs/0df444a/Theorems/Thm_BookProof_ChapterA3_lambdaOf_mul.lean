-- Prove2me | Theorems.Thm_BookProof_ChapterA3_lambdaOf_mul
-- name    : BookProof.ChapterA3.lambdaOf_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T12:32:27.547772+00:00
-- url     : https://prove2.me/theorems/ddb10ead-bf2e-458e-9fd5-850fbbcd3d1b
-- title:
--   `BookProof.ChapterA3.lambdaOf_mul` {S₁ S₂ : Matrix (Fin 4) (Fin 4) ℝ} (h1 : IsPin S₁) (h2 : IsPin S₂) : LambdaOf (S₁ * S₂) = LambdaOf S₁ * LambdaOf S₂
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3c`.
--
--   `BookProof.ChapterA3.lambdaOf_mul` {S₁ S₂ : Matrix (Fin 4) (Fin 4) ℝ} (h1 : IsPin S₁) (h2 : IsPin S₂) : LambdaOf (S₁ * S₂) = LambdaOf S₁ * LambdaOf S₂
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.lambdaOf_mul`.

-- Generated from ChapterA3c.lean — theorem BookProof.ChapterA3.lambdaOf_mul
import Mathlib
import Definitions.Def_ChapterA3c
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.lambdaOf_mul {S₁ S₂ : Matrix (Fin 4) (Fin 4) ℝ}
    (h1 : IsPin S₁) (h2 : IsPin S₂) :
    LambdaOf (S₁ * S₂) = LambdaOf S₁ * LambdaOf S₂ := by sorry
