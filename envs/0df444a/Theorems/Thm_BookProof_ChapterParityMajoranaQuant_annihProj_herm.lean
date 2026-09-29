-- Prove2me | Theorems.Thm_BookProof_ChapterParityMajoranaQuant_annihProj_herm
-- name    : BookProof.ChapterParityMajoranaQuant.annihProj_herm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:02:22.456013+00:00
-- url     : https://prove2.me/theorems/86f9c6ca-d5c2-4f61-b10d-d4bb848a1b9f
-- title:
--   The annihilation projection is Hermitian (an orthogonal projection)
-- statement:
--   The annihilation projection is Hermitian (an orthogonal projection).
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterParityMajoranaQuant.annihProj_herm` (module `BookProof.ParityMajoranaQuant`), line-linked source: `ChapterParityMajoranaQuant.lean` lines 132–136.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterParityMajoranaQuant.lean#L132-L136

-- Generated from ChapterParityMajoranaQuant.lean — theorem BookProof.ChapterParityMajoranaQuant.annihProj_herm
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant










open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

theorem BookProof.ChapterParityMajoranaQuant.annihProj_herm (hskew : Jᴴ = -J) : (annihProj J)ᴴ = annihProj J := by sorry
