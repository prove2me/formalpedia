-- Prove2me | Theorems.Thm_BookProof_ChapterA3_nullConj_iff_form
-- name    : BookProof.ChapterA3.nullConj_iff_form
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:11:24.417706+00:00
-- url     : https://prove2.me/theorems/7b6f1207-5cc1-45ea-98cb-c18637248604
-- title:
--   `BookProof.ChapterA3.nullConj_iff_form` (T : Matrix (Fin 2) (Fin 2) ℂ) : Tᴴ * (pauliσ 0 + pauliσ 3) * T = pauliσ 0 + pauliσ 3 ↔ T 0 1 = 0 ∧ Complex.normSq (T 0 0) = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4d`.
--
--   `BookProof.ChapterA3.nullConj_iff_form` (T : Matrix (Fin 2) (Fin 2) ℂ) : Tᴴ * (pauliσ 0 + pauliσ 3) * T = pauliσ 0 + pauliσ 3 ↔ T 0 1 = 0 ∧ Complex.normSq (T 0 0) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.nullConj_iff_form`.

-- Generated from ChapterA4d.lean — theorem BookProof.ChapterA3.nullConj_iff_form
import Mathlib
import Definitions.Def_ChapterA4d
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3h
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.nullConj_iff_form (T : Matrix (Fin 2) (Fin 2) ℂ) :
    Tᴴ * (pauliσ 0 + pauliσ 3) * T = pauliσ 0 + pauliσ 3 ↔
      T 0 1 = 0 ∧ Complex.normSq (T 0 0) = 1 := by sorry
