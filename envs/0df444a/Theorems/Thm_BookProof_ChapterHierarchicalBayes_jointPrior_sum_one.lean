-- Prove2me | Theorems.Thm_BookProof_ChapterHierarchicalBayes_jointPrior_sum_one
-- name    : BookProof.ChapterHierarchicalBayes.jointPrior_sum_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:13:10.4362+00:00
-- url     : https://prove2.me/theorems/1ee20b2b-61b6-4636-9d8d-752062018417
-- title:
--   `BookProof.ChapterHierarchicalBayes.jointPrior_sum_one` (outer : A → ℝ) (inner : A → B → ℝ) (hOuter : ∑ a, outer a = 1) (hInner : ∀ a, ∑ b, inner a b = 1) : ∑ a, ∑ b, jointPrior ou
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHierarchicalBayes`.
--
--   `BookProof.ChapterHierarchicalBayes.jointPrior_sum_one` (outer : A → ℝ) (inner : A → B → ℝ) (hOuter : ∑ a, outer a = 1) (hInner : ∀ a, ∑ b, inner a b = 1) : ∑ a, ∑ b, jointPrior outer inner a b = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterHierarchicalBayes.jointPrior_sum_one`.

-- Generated from ChapterHierarchicalBayes.lean — theorem BookProof.ChapterHierarchicalBayes.jointPrior_sum_one
import Mathlib
import Definitions.Def_ChapterHierarchicalBayes
open BookProof.ChapterHierarchicalBayes


open scoped BigOperators


variable {A B : Type*} [Fintype A] [Fintype B]

theorem BookProof.ChapterHierarchicalBayes.jointPrior_sum_one (outer : A → ℝ) (inner : A → B → ℝ)
    (hOuter : ∑ a, outer a = 1) (hInner : ∀ a, ∑ b, inner a b = 1) :
    ∑ a, ∑ b, jointPrior outer inner a b = 1 := by sorry
