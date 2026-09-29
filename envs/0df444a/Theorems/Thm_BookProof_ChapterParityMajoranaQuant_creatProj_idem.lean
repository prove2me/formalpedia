-- Prove2me | Theorems.Thm_BookProof_ChapterParityMajoranaQuant_creatProj_idem
-- name    : BookProof.ChapterParityMajoranaQuant.creatProj_idem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:04:59.962165+00:00
-- url     : https://prove2.me/theorems/db439cac-29e7-4854-b54a-5035b6e5b128
-- title:
--   The creation projection is idempotent
-- statement:
--   The creation projection is idempotent.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterParityMajoranaQuant.creatProj_idem` (module `BookProof.ParityMajoranaQuant`), line-linked source: `ChapterParityMajoranaQuant.lean` lines 103–112.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterParityMajoranaQuant.lean#L103-L112

-- Generated from ChapterParityMajoranaQuant.lean — theorem BookProof.ChapterParityMajoranaQuant.creatProj_idem
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant










open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

theorem BookProof.ChapterParityMajoranaQuant.creatProj_idem (hJ2 : J * J = -1) : creatProj J * creatProj J = creatProj J := by sorry
