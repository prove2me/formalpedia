-- Prove2me | Theorems.Thm_BookProof_ChapterParityMajoranaQuant_creatProj_herm
-- name    : BookProof.ChapterParityMajoranaQuant.creatProj_herm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:02:56.189637+00:00
-- url     : https://prove2.me/theorems/d8904318-11ef-4d9c-b6ab-ae5a72969b6d
-- title:
--   The creation projection is Hermitian (an orthogonal projection)
-- statement:
--   The creation projection is Hermitian (an orthogonal projection).
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterParityMajoranaQuant.creatProj_herm` (module `BookProof.ParityMajoranaQuant`), line-linked source: `ChapterParityMajoranaQuant.lean` lines 138–142.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterParityMajoranaQuant.lean#L138-L142

-- Generated from ChapterParityMajoranaQuant.lean — theorem BookProof.ChapterParityMajoranaQuant.creatProj_herm
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant










open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

theorem BookProof.ChapterParityMajoranaQuant.creatProj_herm (hskew : Jᴴ = -J) : (creatProj J)ᴴ = creatProj J := by sorry
