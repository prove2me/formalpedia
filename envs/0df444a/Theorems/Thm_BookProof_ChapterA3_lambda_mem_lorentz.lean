-- Prove2me | Theorems.Thm_BookProof_ChapterA3_lambda_mem_lorentz
-- name    : BookProof.ChapterA3.lambda_mem_lorentz
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T12:21:56.830743+00:00
-- url     : https://prove2.me/theorems/7c894f18-ad50-4faf-be41-6d8442602c46
-- title:
--   `BookProof.ChapterA3.lambda_mem_lorentz` (S : Matrix (Fin 4) (Fin 4) ℝ) (hS : IsPin S) : LambdaOf S ∈ LorentzO
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3c`.
--
--   `BookProof.ChapterA3.lambda_mem_lorentz` (S : Matrix (Fin 4) (Fin 4) ℝ) (hS : IsPin S) : LambdaOf S ∈ LorentzO
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.lambda_mem_lorentz`.

-- Generated from ChapterA3c.lean — theorem BookProof.ChapterA3.lambda_mem_lorentz
import Mathlib
import Definitions.Def_ChapterA3c
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.lambda_mem_lorentz (S : Matrix (Fin 4) (Fin 4) ℝ) (hS : IsPin S) :
    LambdaOf S ∈ LorentzO := by sorry
