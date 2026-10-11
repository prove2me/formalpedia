-- Prove2me | Theorems.Thm_BookProof_ChapterTrajectory_jointProb_sum_final_eq_midProb
-- name    : BookProof.ChapterTrajectory.jointProb_sum_final_eq_midProb
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:26:58.588969+00:00
-- url     : https://prove2.me/theorems/e7ae254d-4a13-44e1-a2e4-a8700d201a46
-- title:
--   `BookProof.ChapterTrajectory.jointProb_sum_final_eq_midProb` (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (hV : Vᴴ * V = 1) (a : Fin n) : ∑ f, jointProb U V psi f a = midProb
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTrajectory`.
--
--   `BookProof.ChapterTrajectory.jointProb_sum_final_eq_midProb` (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (hV : Vᴴ * V = 1) (a : Fin n) : ∑ f, jointProb U V psi f a = midProb U psi a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterTrajectory.jointProb_sum_final_eq_midProb`.

-- Generated from ChapterTrajectory.lean — theorem BookProof.ChapterTrajectory.jointProb_sum_final_eq_midProb
import Mathlib
import Definitions.Def_ChapterTrajectory
open BookProof.ChapterTrajectory


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterTrajectory.jointProb_sum_final_eq_midProb (U V : Matrix (Fin n) (Fin n) ℂ)
    (psi : Fin n → ℂ) (hV : Vᴴ * V = 1) (a : Fin n) :
    ∑ f, jointProb U V psi f a = midProb U psi a := by sorry
