-- Prove2me | Theorems.Thm_BookProof_ChapterHierarchicalBayes_outerPosterior_eq_bayesUpdate
-- name    : BookProof.ChapterHierarchicalBayes.outerPosterior_eq_bayesUpdate
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:14:13.580193+00:00
-- url     : https://prove2.me/theorems/6a898973-bf07-447a-8686-cf30981a08ec
-- title:
--   `BookProof.ChapterHierarchicalBayes.outerPosterior_eq_bayesUpdate` (outer : A → ℝ) (inner : A → B → ℝ) (likelihood : A → B → ℝ) : outerPosterior outer inner likelihood = BookProof.
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHierarchicalBayes`.
--
--   `BookProof.ChapterHierarchicalBayes.outerPosterior_eq_bayesUpdate` (outer : A → ℝ) (inner : A → B → ℝ) (likelihood : A → B → ℝ) : outerPosterior outer inner likelihood = BookProof.ChapterSequentialBayes.bayesUpdate outer (marginalLikelihood inner likelihood)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterHierarchicalBayes.outerPosterior_eq_bayesUpdate`.

-- Generated from ChapterHierarchicalBayes.lean — theorem BookProof.ChapterHierarchicalBayes.outerPosterior_eq_bayesUpdate
import Mathlib
import Definitions.Def_ChapterHierarchicalBayes
import Definitions.Def_ChapterSequentialBayes
open BookProof.ChapterSequentialBayes
open BookProof.ChapterHierarchicalBayes


open scoped BigOperators


variable {A B : Type*} [Fintype A] [Fintype B]

theorem BookProof.ChapterHierarchicalBayes.outerPosterior_eq_bayesUpdate (outer : A → ℝ) (inner : A → B → ℝ)
    (likelihood : A → B → ℝ) :
    outerPosterior outer inner likelihood =
      BookProof.ChapterSequentialBayes.bayesUpdate outer
        (marginalLikelihood inner likelihood) := by sorry
