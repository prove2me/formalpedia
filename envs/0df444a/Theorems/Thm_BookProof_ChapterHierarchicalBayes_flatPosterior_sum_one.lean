-- Prove2me | Theorems.Thm_BookProof_ChapterHierarchicalBayes_flatPosterior_sum_one
-- name    : BookProof.ChapterHierarchicalBayes.flatPosterior_sum_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:13:22.005985+00:00
-- url     : https://prove2.me/theorems/ac79f386-ae8d-4027-add4-74024930fa0e
-- title:
--   `BookProof.ChapterHierarchicalBayes.flatPosterior_sum_one` (outer : A → ℝ) (inner : A → B → ℝ) (likelihood : A → B → ℝ) (hEvidence : 0 < hierEvidence outer inner likelihood) : ∑ a,
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHierarchicalBayes`.
--
--   `BookProof.ChapterHierarchicalBayes.flatPosterior_sum_one` (outer : A → ℝ) (inner : A → B → ℝ) (likelihood : A → B → ℝ) (hEvidence : 0 < hierEvidence outer inner likelihood) : ∑ a, ∑ b, flatPosterior outer inner likelihood a b = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterHierarchicalBayes.flatPosterior_sum_one`.

-- Generated from ChapterHierarchicalBayes.lean — theorem BookProof.ChapterHierarchicalBayes.flatPosterior_sum_one
import Mathlib
import Definitions.Def_ChapterHierarchicalBayes
open BookProof.ChapterHierarchicalBayes


open scoped BigOperators


variable {A B : Type*} [Fintype A] [Fintype B]

theorem BookProof.ChapterHierarchicalBayes.flatPosterior_sum_one (outer : A → ℝ) (inner : A → B → ℝ)
    (likelihood : A → B → ℝ)
    (hEvidence : 0 < hierEvidence outer inner likelihood) :
    ∑ a, ∑ b, flatPosterior outer inner likelihood a b = 1 := by sorry
