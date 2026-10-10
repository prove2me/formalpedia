-- Prove2me | Theorems.Thm_BookProof_ChapterObservableOperator_expectation_outerProj
-- name    : BookProof.ChapterObservableOperator.expectation_outerProj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:39:50.694651+00:00
-- url     : https://prove2.me/theorems/3c7d0ffb-9a37-4c84-88a0-b7221ddce413
-- title:
--   `BookProof.ChapterObservableOperator.expectation_outerProj` (k q : EuclideanSpace ℂ (Fin n)) : expectation (outerProj k) q = ((‖(inner ℂ k q : ℂ)‖ ^ 2 : ℝ) : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterObservableOperator`.
--
--   `BookProof.ChapterObservableOperator.expectation_outerProj` (k q : EuclideanSpace ℂ (Fin n)) : expectation (outerProj k) q = ((‖(inner ℂ k q : ℂ)‖ ^ 2 : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterObservableOperator.expectation_outerProj`.

-- Generated from ChapterObservableOperator.lean — theorem BookProof.ChapterObservableOperator.expectation_outerProj
import Mathlib
import Definitions.Def_ChapterObservableOperator
open BookProof.ChapterObservableOperator


open scoped BigOperators

noncomputable section


variable {n m : ℕ}

theorem BookProof.ChapterObservableOperator.expectation_outerProj (k q : EuclideanSpace ℂ (Fin n)) :
    expectation (outerProj k) q = ((‖(inner ℂ k q : ℂ)‖ ^ 2 : ℝ) : ℂ) := by sorry
