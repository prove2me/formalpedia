-- Prove2me | Theorems.Thm_BookProof_ChapterHierarchicalBayesComposition_compKernel_normalized
-- name    : BookProof.ChapterHierarchicalBayesComposition.compKernel_normalized
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:14:13.790081+00:00
-- url     : https://prove2.me/theorems/37b8912c-8552-4687-8032-8f1bc2f54f2e
-- title:
--   `BookProof.ChapterHierarchicalBayesComposition.compKernel_normalized` (k₁ : A → B → ℝ) (k₂ : B → C → ℝ) (h₁ : IsNormalizedKernel k₁) (h₂ : IsNormalizedKernel k₂) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHierarchicalBayesComposition`.
--
--   `BookProof.ChapterHierarchicalBayesComposition.compKernel_normalized` (k₁ : A → B → ℝ) (k₂ : B → C → ℝ) (h₁ : IsNormalizedKernel k₁) (h₂ : IsNormalizedKernel k₂) : IsNormalizedKernel (compKernel k₁ k₂)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterHierarchicalBayesComposition.compKernel_normalized`.

-- Generated from ChapterHierarchicalBayesComposition.lean — theorem BookProof.ChapterHierarchicalBayesComposition.compKernel_normalized
import Mathlib
import Definitions.Def_ChapterHierarchicalBayesComposition
open BookProof.ChapterHierarchicalBayesComposition


open scoped BigOperators


variable {A B C D : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

theorem BookProof.ChapterHierarchicalBayesComposition.compKernel_normalized (k₁ : A → B → ℝ) (k₂ : B → C → ℝ)
    (h₁ : IsNormalizedKernel k₁) (h₂ : IsNormalizedKernel k₂) :
    IsNormalizedKernel (compKernel k₁ k₂) := by sorry
