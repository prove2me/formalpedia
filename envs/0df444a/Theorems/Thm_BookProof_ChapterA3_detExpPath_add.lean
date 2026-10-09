-- Prove2me | Theorems.Thm_BookProof_ChapterA3_detExpPath_add
-- name    : BookProof.ChapterA3.detExpPath_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:47:14.33119+00:00
-- url     : https://prove2.me/theorems/8eee8b3f-94ca-4c2c-9d34-9dec8b672888
-- title:
--   `BookProof.ChapterA3.detExpPath_add` (A : Matrix (Fin n) (Fin n) ℝ) (s t : ℝ) : detExpPath A (s + t) = detExpPath A s * detExpPath A t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3f`.
--
--   `BookProof.ChapterA3.detExpPath_add` (A : Matrix (Fin n) (Fin n) ℝ) (s t : ℝ) : detExpPath A (s + t) = detExpPath A s * detExpPath A t
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.detExpPath_add`.

-- Generated from ChapterA3f.lean — theorem BookProof.ChapterA3.detExpPath_add
import Mathlib
import Definitions.Def_ChapterA3f
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix NormedSpace
open scoped Norms.Operator


variable {n : ℕ}

theorem BookProof.ChapterA3.detExpPath_add (A : Matrix (Fin n) (Fin n) ℝ) (s t : ℝ) :
    detExpPath A (s + t) = detExpPath A s * detExpPath A t := by sorry
