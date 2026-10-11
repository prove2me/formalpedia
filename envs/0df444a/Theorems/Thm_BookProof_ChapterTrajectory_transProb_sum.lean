-- Prove2me | Theorems.Thm_BookProof_ChapterTrajectory_transProb_sum
-- name    : BookProof.ChapterTrajectory.transProb_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:26:53.6341+00:00
-- url     : https://prove2.me/theorems/312f13f8-a0e0-486d-94b8-73ade1c140f9
-- title:
--   `BookProof.ChapterTrajectory.transProb_sum` (V : Matrix (Fin n) (Fin n) ℂ) (hV : Vᴴ * V = 1) (a : Fin n) : ∑ f, transProb V f a = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTrajectory`.
--
--   `BookProof.ChapterTrajectory.transProb_sum` (V : Matrix (Fin n) (Fin n) ℂ) (hV : Vᴴ * V = 1) (a : Fin n) : ∑ f, transProb V f a = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterTrajectory.transProb_sum`.

-- Generated from ChapterTrajectory.lean — theorem BookProof.ChapterTrajectory.transProb_sum
import Mathlib
import Definitions.Def_ChapterTrajectory
open BookProof.ChapterTrajectory


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterTrajectory.transProb_sum (V : Matrix (Fin n) (Fin n) ℂ) (hV : Vᴴ * V = 1)
    (a : Fin n) : ∑ f, transProb V f a = 1 := by sorry
