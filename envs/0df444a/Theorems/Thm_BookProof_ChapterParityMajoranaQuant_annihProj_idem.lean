-- Prove2me | Theorems.Thm_BookProof_ChapterParityMajoranaQuant_annihProj_idem
-- name    : BookProof.ChapterParityMajoranaQuant.annihProj_idem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:03:33.274484+00:00
-- url     : https://prove2.me/theorems/cb782c85-be5e-4b02-a422-374279930782
-- title:
--   The annihilation projection is idempotent
-- statement:
--   The annihilation projection is idempotent.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterParityMajoranaQuant.annihProj_idem` (module `BookProof.ParityMajoranaQuant`), line-linked source: `ChapterParityMajoranaQuant.lean` lines 92–101.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterParityMajoranaQuant.lean#L92-L101

-- Generated from ChapterParityMajoranaQuant.lean — theorem BookProof.ChapterParityMajoranaQuant.annihProj_idem
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant










open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

theorem BookProof.ChapterParityMajoranaQuant.annihProj_idem (hJ2 : J * J = -1) : annihProj J * annihProj J = annihProj J := by sorry
