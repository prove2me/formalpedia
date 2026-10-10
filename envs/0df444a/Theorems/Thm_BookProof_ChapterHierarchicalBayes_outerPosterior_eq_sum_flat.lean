-- Prove2me | Theorems.Thm_BookProof_ChapterHierarchicalBayes_outerPosterior_eq_sum_flat
-- name    : BookProof.ChapterHierarchicalBayes.outerPosterior_eq_sum_flat
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:13:11.62385+00:00
-- url     : https://prove2.me/theorems/1e4b8902-46ca-4711-858a-1c11321585f4
-- title:
--   `BookProof.ChapterHierarchicalBayes.outerPosterior_eq_sum_flat` (outer : A → ℝ) (inner : A → B → ℝ) (likelihood : A → B → ℝ) (a : A) : outerPosterior outer inner likelihood a = ∑ b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHierarchicalBayes`.
--
--   `BookProof.ChapterHierarchicalBayes.outerPosterior_eq_sum_flat` (outer : A → ℝ) (inner : A → B → ℝ) (likelihood : A → B → ℝ) (a : A) : outerPosterior outer inner likelihood a = ∑ b, flatPosterior outer inner likelihood a b
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterHierarchicalBayes.outerPosterior_eq_sum_flat`.

-- Generated from ChapterHierarchicalBayes.lean — theorem BookProof.ChapterHierarchicalBayes.outerPosterior_eq_sum_flat
import Mathlib
import Definitions.Def_ChapterHierarchicalBayes
open BookProof.ChapterHierarchicalBayes


open scoped BigOperators


variable {A B : Type*} [Fintype A] [Fintype B]

theorem BookProof.ChapterHierarchicalBayes.outerPosterior_eq_sum_flat (outer : A → ℝ) (inner : A → B → ℝ)
    (likelihood : A → B → ℝ) (a : A) :
    outerPosterior outer inner likelihood a =
      ∑ b, flatPosterior outer inner likelihood a b := by sorry
