-- Prove2me | Theorems.Thm_BookProof_ChapterHierarchicalBayesComposition_compKernel_assoc
-- name    : BookProof.ChapterHierarchicalBayesComposition.compKernel_assoc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:14:17.410007+00:00
-- url     : https://prove2.me/theorems/f4479b89-03a8-44b1-aece-c75ce3fd649f
-- title:
--   `BookProof.ChapterHierarchicalBayesComposition.compKernel_assoc` (k₁ : A → B → ℝ) (k₂ : B → C → ℝ) (k₃ : C → D → ℝ) : compKernel (compKernel k₁ k₂) k₃ = compKernel...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHierarchicalBayesComposition`.
--
--   `BookProof.ChapterHierarchicalBayesComposition.compKernel_assoc` (k₁ : A → B → ℝ) (k₂ : B → C → ℝ) (k₃ : C → D → ℝ) : compKernel (compKernel k₁ k₂) k₃ = compKernel k₁ (compKernel k₂ k₃)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterHierarchicalBayesComposition.compKernel_assoc`.

-- Generated from ChapterHierarchicalBayesComposition.lean — theorem BookProof.ChapterHierarchicalBayesComposition.compKernel_assoc
import Mathlib
import Definitions.Def_ChapterHierarchicalBayesComposition
open BookProof.ChapterHierarchicalBayesComposition


open scoped BigOperators


variable {A B C D : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

theorem BookProof.ChapterHierarchicalBayesComposition.compKernel_assoc (k₁ : A → B → ℝ) (k₂ : B → C → ℝ)
    (k₃ : C → D → ℝ) :
    compKernel (compKernel k₁ k₂) k₃ = compKernel k₁ (compKernel k₂ k₃) := by sorry
