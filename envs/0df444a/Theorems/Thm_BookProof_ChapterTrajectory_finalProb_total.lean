-- Prove2me | Theorems.Thm_BookProof_ChapterTrajectory_finalProb_total
-- name    : BookProof.ChapterTrajectory.finalProb_total
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:27:09.699499+00:00
-- url     : https://prove2.me/theorems/68046587-ca17-4912-ba8d-f24eb0347315
-- title:
--   `BookProof.ChapterTrajectory.finalProb_total` (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (hpsi : ∑ a, ‖psi a‖ ^ 2 = 1) : ∑ f, finalProb
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTrajectory`.
--
--   `BookProof.ChapterTrajectory.finalProb_total` (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (hpsi : ∑ a, ‖psi a‖ ^ 2 = 1) : ∑ f, finalProb U V psi f = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterTrajectory.finalProb_total`.

-- Generated from ChapterTrajectory.lean — theorem BookProof.ChapterTrajectory.finalProb_total
import Mathlib
import Definitions.Def_ChapterTrajectory
open BookProof.ChapterTrajectory


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterTrajectory.finalProb_total (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (hpsi : ∑ a, ‖psi a‖ ^ 2 = 1) :
    ∑ f, finalProb U V psi f = 1 := by sorry
