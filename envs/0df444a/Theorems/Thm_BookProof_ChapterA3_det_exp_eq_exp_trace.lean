-- Prove2me | Theorems.Thm_BookProof_ChapterA3_det_exp_eq_exp_trace
-- name    : BookProof.ChapterA3.det_exp_eq_exp_trace
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:48:07.433975+00:00
-- url     : https://prove2.me/theorems/c8d29638-90ff-49f9-a185-2b10a548edfb
-- title:
--   `BookProof.ChapterA3.det_exp_eq_exp_trace` (A : Matrix (Fin n) (Fin n) ℝ) : (NormedSpace.exp A).det = Real.exp A.trace
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3f`.
--
--   `BookProof.ChapterA3.det_exp_eq_exp_trace` (A : Matrix (Fin n) (Fin n) ℝ) : (NormedSpace.exp A).det = Real.exp A.trace
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.det_exp_eq_exp_trace`.

-- Generated from ChapterA3f.lean — theorem BookProof.ChapterA3.det_exp_eq_exp_trace
import Mathlib
import Definitions.Def_ChapterA3f
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix NormedSpace
open scoped Norms.Operator


variable {n : ℕ}

theorem BookProof.ChapterA3.det_exp_eq_exp_trace (A : Matrix (Fin n) (Fin n) ℝ) :
    (NormedSpace.exp A).det = Real.exp A.trace := by sorry
