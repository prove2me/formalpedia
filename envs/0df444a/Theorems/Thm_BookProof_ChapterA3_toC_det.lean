-- Prove2me | Theorems.Thm_BookProof_ChapterA3_toC_det
-- name    : BookProof.ChapterA3.toC_det
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T12:03:26.750931+00:00
-- url     : https://prove2.me/theorems/30bf93cd-0fd9-40f2-9390-34798842dedb
-- title:
--   `BookProof.ChapterA3.toC_det` (M : Matrix (Fin 4) (Fin 4) ℝ) : (toC M).det = (M.det : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3b`.
--
--   `BookProof.ChapterA3.toC_det` (M : Matrix (Fin 4) (Fin 4) ℝ) : (toC M).det = (M.det : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.toC_det`.

-- Generated from ChapterA3b.lean — theorem BookProof.ChapterA3.toC_det
import Mathlib
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.toC_det (M : Matrix (Fin 4) (Fin 4) ℝ) : (toC M).det = (M.det : ℂ) := by sorry
