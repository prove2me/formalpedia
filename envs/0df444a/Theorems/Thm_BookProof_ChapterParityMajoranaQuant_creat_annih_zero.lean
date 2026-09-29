-- Prove2me | Theorems.Thm_BookProof_ChapterParityMajoranaQuant_creat_annih_zero
-- name    : BookProof.ChapterParityMajoranaQuant.creat_annih_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:05:44.821103+00:00
-- url     : https://prove2.me/theorems/85b1fc04-2b8b-4f72-b94d-3e9ef78edb2f
-- title:
--   The two projections are complementary: `creatProj · annihProj = 0`
-- statement:
--   The two projections are complementary: `creatProj · annihProj = 0`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterParityMajoranaQuant.creat_annih_zero` (module `BookProof.ParityMajoranaQuant`), line-linked source: `ChapterParityMajoranaQuant.lean` lines 123–130.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterParityMajoranaQuant.lean#L123-L130

-- Generated from ChapterParityMajoranaQuant.lean — theorem BookProof.ChapterParityMajoranaQuant.creat_annih_zero
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant










open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

theorem BookProof.ChapterParityMajoranaQuant.creat_annih_zero (hJ2 : J * J = -1) : creatProj J * annihProj J = 0 := by sorry
