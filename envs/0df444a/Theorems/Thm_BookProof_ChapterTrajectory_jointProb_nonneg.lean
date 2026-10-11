-- Prove2me | Theorems.Thm_BookProof_ChapterTrajectory_jointProb_nonneg
-- name    : BookProof.ChapterTrajectory.jointProb_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:27:28.700513+00:00
-- url     : https://prove2.me/theorems/0370cc18-9a77-44c1-9ae7-f99e3348cd71
-- title:
--   `BookProof.ChapterTrajectory.jointProb_nonneg` (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (f a : Fin n) : 0 ≤ jointProb U V psi f a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTrajectory`.
--
--   `BookProof.ChapterTrajectory.jointProb_nonneg` (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ) (f a : Fin n) : 0 ≤ jointProb U V psi f a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterTrajectory.jointProb_nonneg`.

-- Generated from ChapterTrajectory.lean — theorem BookProof.ChapterTrajectory.jointProb_nonneg
import Mathlib
import Definitions.Def_ChapterTrajectory
open BookProof.ChapterTrajectory


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterTrajectory.jointProb_nonneg (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (f a : Fin n) : 0 ≤ jointProb U V psi f a := by sorry
