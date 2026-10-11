-- Prove2me | Theorems.Thm_BookProof_ChapterTrajectory_condProb_sum
-- name    : BookProof.ChapterTrajectory.condProb_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:27:17.072698+00:00
-- url     : https://prove2.me/theorems/db900201-1a77-4405-a9e9-7076a7be6fd8
-- title:
--   `BookProof.ChapterTrajectory.condProb_sum` (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (f : Fin n) (hf : finalProb U V psi f ≠ 0) : ∑ a, condProb U V psi f a = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTrajectory`.
--
--   `BookProof.ChapterTrajectory.condProb_sum` (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (f : Fin n) (hf : finalProb U V psi f ≠ 0) : ∑ a, condProb U V psi f a = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterTrajectory.condProb_sum`.

-- Generated from ChapterTrajectory.lean — theorem BookProof.ChapterTrajectory.condProb_sum
import Mathlib
import Definitions.Def_ChapterTrajectory
open BookProof.ChapterTrajectory


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterTrajectory.condProb_sum (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (f : Fin n) (hf : finalProb U V psi f ≠ 0) :
    ∑ a, condProb U V psi f a = 1 := by sorry
