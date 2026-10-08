-- Prove2me | Theorems.Thm_BookProof_ChapterA3_hasDerivAt_detExpPath
-- name    : BookProof.ChapterA3.hasDerivAt_detExpPath
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:47:56.258522+00:00
-- url     : https://prove2.me/theorems/14b4efb2-dc52-4e07-8f84-345c1f4d5c3c
-- title:
--   `BookProof.ChapterA3.hasDerivAt_detExpPath` (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : HasDerivAt (detExpPath A) (A.trace * detExpPath A t) t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3f`.
--
--   `BookProof.ChapterA3.hasDerivAt_detExpPath` (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : HasDerivAt (detExpPath A) (A.trace * detExpPath A t) t
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.hasDerivAt_detExpPath`.

-- Generated from ChapterA3f.lean — theorem BookProof.ChapterA3.hasDerivAt_detExpPath
import Mathlib
import Definitions.Def_ChapterA3f
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix NormedSpace
open scoped Norms.Operator


variable {n : ℕ}

theorem BookProof.ChapterA3.hasDerivAt_detExpPath (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (detExpPath A) (A.trace * detExpPath A t) t := by sorry
