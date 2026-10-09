-- Prove2me | Theorems.Thm_BookProof_ChapterHierarchicalBayes_jointPrior_nonneg
-- name    : BookProof.ChapterHierarchicalBayes.jointPrior_nonneg
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:13:04.57401+00:00
-- url     : https://prove2.me/theorems/41d333b8-f0bc-4a37-8394-effa84fbb36b
-- title:
--   `BookProof.ChapterHierarchicalBayes.jointPrior_nonneg` (outer : A → ℝ) (inner : A → B → ℝ) (hOuter : ∀ a, 0 ≤ outer a) (hInner : ∀ a b, 0 ≤ inner a b) : ∀ a b, 0 ≤...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHierarchicalBayes`.
--
--   `BookProof.ChapterHierarchicalBayes.jointPrior_nonneg` (outer : A → ℝ) (inner : A → B → ℝ) (hOuter : ∀ a, 0 ≤ outer a) (hInner : ∀ a b, 0 ≤ inner a b) : ∀ a b, 0 ≤ jointPrior outer inner a b
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterHierarchicalBayes.jointPrior_nonneg`.

-- Generated from ChapterHierarchicalBayes.lean — theorem BookProof.ChapterHierarchicalBayes.jointPrior_nonneg
import Mathlib
import Definitions.Def_ChapterHierarchicalBayes
open BookProof.ChapterHierarchicalBayes


open scoped BigOperators


variable {A B : Type*} [Fintype A] [Fintype B]

theorem BookProof.ChapterHierarchicalBayes.jointPrior_nonneg (outer : A → ℝ) (inner : A → B → ℝ)
    (hOuter : ∀ a, 0 ≤ outer a) (hInner : ∀ a b, 0 ≤ inner a b) :
    ∀ a b, 0 ≤ jointPrior outer inner a b := by sorry
