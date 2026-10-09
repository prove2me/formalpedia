-- Prove2me | Theorems.Thm_BookProof_ChapterA3_hasDerivAt_det_line
-- name    : BookProof.ChapterA3.hasDerivAt_det_line
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:47:25.614061+00:00
-- url     : https://prove2.me/theorems/9d051383-2759-414f-8ec8-5fbaafb7ba16
-- title:
--   `BookProof.ChapterA3.hasDerivAt_det_line` (A : Matrix (Fin n) (Fin n) ℝ) : HasDerivAt (fun t : ℝ => (1 + t • A).det) A.trace 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3f`.
--
--   `BookProof.ChapterA3.hasDerivAt_det_line` (A : Matrix (Fin n) (Fin n) ℝ) : HasDerivAt (fun t : ℝ => (1 + t • A).det) A.trace 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.hasDerivAt_det_line`.

-- Generated from ChapterA3f.lean — theorem BookProof.ChapterA3.hasDerivAt_det_line
import Mathlib
import Definitions.Def_ChapterA3f
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix NormedSpace
open scoped Norms.Operator


variable {n : ℕ}

theorem BookProof.ChapterA3.hasDerivAt_det_line (A : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • A).det) A.trace 0 := by sorry
