-- Prove2me | Theorems.Thm_BookProof_ChapterHierarchicalBayesComposition_compKernel_nonnegative
-- name    : BookProof.ChapterHierarchicalBayesComposition.compKernel_nonnegative
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:14:22.14197+00:00
-- url     : https://prove2.me/theorems/5f53267b-e847-4e09-9b85-d4e003b2eb07
-- title:
--   `BookProof.ChapterHierarchicalBayesComposition.compKernel_nonnegative` (k₁ : A → B → ℝ) (k₂ : B → C → ℝ) (h₁ : IsNonnegativeKernel k₁) (h₂ : IsNonnegativeKernel k₂) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHierarchicalBayesComposition`.
--
--   `BookProof.ChapterHierarchicalBayesComposition.compKernel_nonnegative` (k₁ : A → B → ℝ) (k₂ : B → C → ℝ) (h₁ : IsNonnegativeKernel k₁) (h₂ : IsNonnegativeKernel k₂) : IsNonnegativeKernel (compKernel k₁ k₂)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterHierarchicalBayesComposition.compKernel_nonnegative`.

-- Generated from ChapterHierarchicalBayesComposition.lean — theorem BookProof.ChapterHierarchicalBayesComposition.compKernel_nonnegative
import Mathlib
import Definitions.Def_ChapterHierarchicalBayesComposition
open BookProof.ChapterHierarchicalBayesComposition


open scoped BigOperators


variable {A B C D : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

theorem BookProof.ChapterHierarchicalBayesComposition.compKernel_nonnegative (k₁ : A → B → ℝ) (k₂ : B → C → ℝ)
    (h₁ : IsNonnegativeKernel k₁) (h₂ : IsNonnegativeKernel k₂) :
    IsNonnegativeKernel (compKernel k₁ k₂) := by sorry
