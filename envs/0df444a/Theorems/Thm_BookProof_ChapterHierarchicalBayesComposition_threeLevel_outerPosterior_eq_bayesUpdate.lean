-- Prove2me | Theorems.Thm_BookProof_ChapterHierarchicalBayesComposition_threeLevel_outerPosterior_eq_bayesUpdate
-- name    : BookProof.ChapterHierarchicalBayesComposition.threeLevel_outerPosterior_eq_bayesUpdate
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:16:40.566027+00:00
-- url     : https://prove2.me/theorems/1d85766c-bd46-49a7-9b63-b2750ed426d4
-- title:
--   `BookProof.ChapterHierarchicalBayesComposition.threeLevel_outerPosterior_eq_bayesUpdate` (outer : A → ℝ) (k₁ : A → B → ℝ) (k₂ : B → C → ℝ) (likelihood : C → ℝ) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHierarchicalBayesComposition`.
--
--   `BookProof.ChapterHierarchicalBayesComposition.threeLevel_outerPosterior_eq_bayesUpdate` (outer : A → ℝ) (k₁ : A → B → ℝ) (k₂ : B → C → ℝ) (likelihood : C → ℝ) : BookProof.ChapterHierarchicalBayes.outerPosterior outer (compKernel k₁ k₂) (fun _ c => likelihood c) = BookProof.ChapterSequentialBayes.bayesUpdate outer (BookProof.ChapterHierarchicalBayes.marginalLikelihood (compKernel k₁ k₂) (fun _ c => likelihood c))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterHierarchicalBayesComposition.threeLevel_outerPosterior_eq_bayesUpdate`.

-- Generated from ChapterHierarchicalBayesComposition.lean — theorem BookProof.ChapterHierarchicalBayesComposition.threeLevel_outerPosterior_eq_bayesUpdate
import Mathlib
import Definitions.Def_ChapterHierarchicalBayesComposition
import Definitions.Def_ChapterHierarchicalBayes
import Definitions.Def_ChapterSequentialBayes
open BookProof.ChapterHierarchicalBayes
open BookProof.ChapterSequentialBayes
open BookProof.ChapterHierarchicalBayesComposition


open scoped BigOperators


variable {A B C D : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

theorem BookProof.ChapterHierarchicalBayesComposition.threeLevel_outerPosterior_eq_bayesUpdate (outer : A → ℝ)
    (k₁ : A → B → ℝ) (k₂ : B → C → ℝ) (likelihood : C → ℝ) :
    BookProof.ChapterHierarchicalBayes.outerPosterior outer
        (compKernel k₁ k₂) (fun _ c => likelihood c) =
      BookProof.ChapterSequentialBayes.bayesUpdate outer
        (BookProof.ChapterHierarchicalBayes.marginalLikelihood
          (compKernel k₁ k₂) (fun _ c => likelihood c)) := by sorry
