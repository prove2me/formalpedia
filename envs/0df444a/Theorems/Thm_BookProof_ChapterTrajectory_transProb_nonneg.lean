-- Prove2me | Theorems.Thm_BookProof_ChapterTrajectory_transProb_nonneg
-- name    : BookProof.ChapterTrajectory.transProb_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:26:28.169387+00:00
-- url     : https://prove2.me/theorems/427f203b-8b7a-4b8b-95a0-f0888b8d39d9
-- title:
--   `BookProof.ChapterTrajectory.transProb_nonneg` (V : Matrix (Fin n) (Fin n) ℂ) (f a : Fin n) : 0 ≤ transProb V f a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTrajectory`.
--
--   `BookProof.ChapterTrajectory.transProb_nonneg` (V : Matrix (Fin n) (Fin n) ℂ) (f a : Fin n) : 0 ≤ transProb V f a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterTrajectory.transProb_nonneg`.

-- Generated from ChapterTrajectory.lean — theorem BookProof.ChapterTrajectory.transProb_nonneg
import Mathlib
import Definitions.Def_ChapterTrajectory
open BookProof.ChapterTrajectory


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterTrajectory.transProb_nonneg (V : Matrix (Fin n) (Fin n) ℂ) (f a : Fin n) :
    0 ≤ transProb V f a := by sorry
