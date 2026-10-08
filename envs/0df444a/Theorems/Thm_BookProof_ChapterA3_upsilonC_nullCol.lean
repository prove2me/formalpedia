-- Prove2me | Theorems.Thm_BookProof_ChapterA3_upsilonC_nullCol
-- name    : BookProof.ChapterA3.upsilonC_nullCol
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:10:49.398096+00:00
-- url     : https://prove2.me/theorems/a5e72c55-cb14-4c0b-ae30-1418d8d2edcd
-- title:
--   `BookProof.ChapterA3.upsilonC_nullCol` (T : Matrix (Fin 2) (Fin 2) ℂ) (μ : Fin 4) : UpsilonC T μ 0 + UpsilonC T μ 3 = pauliCoeff (Tᴴ * (pauliσ 0 + pauliσ 3) * T) μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4d`.
--
--   `BookProof.ChapterA3.upsilonC_nullCol` (T : Matrix (Fin 2) (Fin 2) ℂ) (μ : Fin 4) : UpsilonC T μ 0 + UpsilonC T μ 3 = pauliCoeff (Tᴴ * (pauliσ 0 + pauliσ 3) * T) μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.upsilonC_nullCol`.

-- Generated from ChapterA4d.lean — theorem BookProof.ChapterA3.upsilonC_nullCol
import Mathlib
import Definitions.Def_ChapterA4d
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3h
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.upsilonC_nullCol (T : Matrix (Fin 2) (Fin 2) ℂ) (μ : Fin 4) :
    UpsilonC T μ 0 + UpsilonC T μ 3 = pauliCoeff (Tᴴ * (pauliσ 0 + pauliσ 3) * T) μ := by sorry
