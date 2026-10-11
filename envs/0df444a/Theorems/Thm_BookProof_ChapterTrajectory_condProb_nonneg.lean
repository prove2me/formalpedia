-- Prove2me | Theorems.Thm_BookProof_ChapterTrajectory_condProb_nonneg
-- name    : BookProof.ChapterTrajectory.condProb_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:27:21.881734+00:00
-- url     : https://prove2.me/theorems/a03abc11-cad5-4130-a6a6-be5ba4be7480
-- title:
--   `BookProof.ChapterTrajectory.condProb_nonneg` (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (f a : Fin n) : 0 ≤ condProb U V psi f a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTrajectory`.
--
--   `BookProof.ChapterTrajectory.condProb_nonneg` (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (f a : Fin n) : 0 ≤ condProb U V psi f a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterTrajectory.condProb_nonneg`.

-- Generated from ChapterTrajectory.lean — theorem BookProof.ChapterTrajectory.condProb_nonneg
import Mathlib
import Definitions.Def_ChapterTrajectory
open BookProof.ChapterTrajectory


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterTrajectory.condProb_nonneg (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (f a : Fin n) : 0 ≤ condProb U V psi f a := by sorry
