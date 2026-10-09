-- Prove2me | Theorems.Thm_BookProof_ChapterEulerStochastic_preservesProb_iff_columnStochastic
-- name    : BookProof.ChapterEulerStochastic.preservesProb_iff_columnStochastic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:44:56.922523+00:00
-- url     : https://prove2.me/theorems/6f61f24d-ca3a-4bd9-9932-3c124bbcd1d4
-- title:
--   `BookProof.ChapterEulerStochastic.preservesProb_iff_columnStochastic` (M : Matrix (Fin 2) (Fin 2) ℝ) : PreservesProb M ↔ (IsProbVec (fun i => M i 0) ∧ IsProbVec (fun i => M i 1))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerStochastic`.
--
--   `BookProof.ChapterEulerStochastic.preservesProb_iff_columnStochastic` (M : Matrix (Fin 2) (Fin 2) ℝ) : PreservesProb M ↔ (IsProbVec (fun i => M i 0) ∧ IsProbVec (fun i => M i 1))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerStochastic.preservesProb_iff_columnStochastic`.

-- Generated from ChapterEulerStochastic.lean — theorem BookProof.ChapterEulerStochastic.preservesProb_iff_columnStochastic
import Mathlib
import Definitions.Def_ChapterEulerStochastic
open BookProof.ChapterEulerStochastic


open scoped Matrix BigOperators

theorem BookProof.ChapterEulerStochastic.preservesProb_iff_columnStochastic (M : Matrix (Fin 2) (Fin 2) ℝ) :
    PreservesProb M ↔
      (IsProbVec (fun i => M i 0) ∧ IsProbVec (fun i => M i 1)) := by sorry
