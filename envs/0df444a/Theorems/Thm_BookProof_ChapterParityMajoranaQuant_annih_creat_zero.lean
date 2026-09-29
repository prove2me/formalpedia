-- Prove2me | Theorems.Thm_BookProof_ChapterParityMajoranaQuant_annih_creat_zero
-- name    : BookProof.ChapterParityMajoranaQuant.annih_creat_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:04:14.018668+00:00
-- url     : https://prove2.me/theorems/11ffbca7-4477-4ede-9035-a79364178ca9
-- title:
--   The two projections are complementary: `annihProj · creatProj = 0`
-- statement:
--   The two projections are complementary: `annihProj · creatProj = 0`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterParityMajoranaQuant.annih_creat_zero` (module `BookProof.ParityMajoranaQuant`), line-linked source: `ChapterParityMajoranaQuant.lean` lines 114–121.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterParityMajoranaQuant.lean#L114-L121

-- Generated from ChapterParityMajoranaQuant.lean — theorem BookProof.ChapterParityMajoranaQuant.annih_creat_zero
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant










open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

theorem BookProof.ChapterParityMajoranaQuant.annih_creat_zero (hJ2 : J * J = -1) : annihProj J * creatProj J = 0 := by sorry
