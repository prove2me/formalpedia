-- Prove2me | Theorems.Thm_BookProof_ChapterTrajectory_midProb_nonneg
-- name    : BookProof.ChapterTrajectory.midProb_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:26:26.962536+00:00
-- url     : https://prove2.me/theorems/ea481277-a0a5-483f-a8b9-d2a225760ac3
-- title:
--   `BookProof.ChapterTrajectory.midProb_nonneg` (U : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (a : Fin n) : 0 ≤ midProb U psi a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTrajectory`.
--
--   `BookProof.ChapterTrajectory.midProb_nonneg` (U : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (a : Fin n) : 0 ≤ midProb U psi a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterTrajectory.midProb_nonneg`.

-- Generated from ChapterTrajectory.lean — theorem BookProof.ChapterTrajectory.midProb_nonneg
import Mathlib
import Definitions.Def_ChapterTrajectory
open BookProof.ChapterTrajectory


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterTrajectory.midProb_nonneg (U : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (a : Fin n) : 0 ≤ midProb U psi a := by sorry
