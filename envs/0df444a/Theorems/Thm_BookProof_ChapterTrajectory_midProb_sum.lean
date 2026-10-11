-- Prove2me | Theorems.Thm_BookProof_ChapterTrajectory_midProb_sum
-- name    : BookProof.ChapterTrajectory.midProb_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:27:06.673606+00:00
-- url     : https://prove2.me/theorems/81a9caee-10c8-42b4-bdb0-242cb942d2b6
-- title:
--   `BookProof.ChapterTrajectory.midProb_sum` (U : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (hU : Uᴴ * U = 1) : ∑ a, midProb U psi a = ∑ a, ‖psi a‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTrajectory`.
--
--   `BookProof.ChapterTrajectory.midProb_sum` (U : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (hU : Uᴴ * U = 1) : ∑ a, midProb U psi a = ∑ a, ‖psi a‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterTrajectory.midProb_sum`.

-- Generated from ChapterTrajectory.lean — theorem BookProof.ChapterTrajectory.midProb_sum
import Mathlib
import Definitions.Def_ChapterTrajectory
open BookProof.ChapterTrajectory


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterTrajectory.midProb_sum (U : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (hU : Uᴴ * U = 1) : ∑ a, midProb U psi a = ∑ a, ‖psi a‖ ^ 2 := by sorry
