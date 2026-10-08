-- Prove2me | Theorems.Thm_BookProof_ChapterA3_hasLambda_unique
-- name    : BookProof.ChapterA3.hasLambda_unique
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T12:20:44.450135+00:00
-- url     : https://prove2.me/theorems/5de656a8-5d75-44df-9d2c-1474e1455a1a
-- title:
--   `BookProof.ChapterA3.hasLambda_unique` {S Λ Λ' : Matrix (Fin 4) (Fin 4) ℝ} (h : HasLambda S Λ) (h' : HasLambda S Λ') : Λ = Λ'
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3c`.
--
--   `BookProof.ChapterA3.hasLambda_unique` {S Λ Λ' : Matrix (Fin 4) (Fin 4) ℝ} (h : HasLambda S Λ) (h' : HasLambda S Λ') : Λ = Λ'
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.hasLambda_unique`.

-- Generated from ChapterA3c.lean — theorem BookProof.ChapterA3.hasLambda_unique
import Mathlib
import Definitions.Def_ChapterA3c
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.hasLambda_unique {S Λ Λ' : Matrix (Fin 4) (Fin 4) ℝ}
    (h : HasLambda S Λ) (h' : HasLambda S Λ') : Λ = Λ' := by sorry
