-- Prove2me | Theorems.Thm_BookProof_ChapterTrajectory_finalProb_nonneg
-- name    : BookProof.ChapterTrajectory.finalProb_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:26:41.125671+00:00
-- url     : https://prove2.me/theorems/9eedf15b-7cad-4b46-967a-3b64fdfe0855
-- title:
--   `BookProof.ChapterTrajectory.finalProb_nonneg` (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (f : Fin n) : 0 ≤ finalProb U V psi f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTrajectory`.
--
--   `BookProof.ChapterTrajectory.finalProb_nonneg` (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (f : Fin n) : 0 ≤ finalProb U V psi f
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterTrajectory.finalProb_nonneg`.

-- Generated from ChapterTrajectory.lean — theorem BookProof.ChapterTrajectory.finalProb_nonneg
import Mathlib
import Definitions.Def_ChapterTrajectory
open BookProof.ChapterTrajectory


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterTrajectory.finalProb_nonneg (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (f : Fin n) : 0 ≤ finalProb U V psi f := by sorry
