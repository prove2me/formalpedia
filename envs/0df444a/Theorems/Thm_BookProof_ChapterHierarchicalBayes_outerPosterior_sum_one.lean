-- Prove2me | Theorems.Thm_BookProof_ChapterHierarchicalBayes_outerPosterior_sum_one
-- name    : BookProof.ChapterHierarchicalBayes.outerPosterior_sum_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:13:35.104632+00:00
-- url     : https://prove2.me/theorems/daaa8088-b32b-4465-9122-9b6a1179bb63
-- title:
--   `BookProof.ChapterHierarchicalBayes.outerPosterior_sum_one` (outer : A → ℝ) (inner : A → B → ℝ) (likelihood : A → B → ℝ) (hEvidence : 0 < hierEvidence outer inner likelihood) : ∑ a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHierarchicalBayes`.
--
--   `BookProof.ChapterHierarchicalBayes.outerPosterior_sum_one` (outer : A → ℝ) (inner : A → B → ℝ) (likelihood : A → B → ℝ) (hEvidence : 0 < hierEvidence outer inner likelihood) : ∑ a, outerPosterior outer inner likelihood a = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterHierarchicalBayes.outerPosterior_sum_one`.

-- Generated from ChapterHierarchicalBayes.lean — theorem BookProof.ChapterHierarchicalBayes.outerPosterior_sum_one
import Mathlib
import Definitions.Def_ChapterHierarchicalBayes
open BookProof.ChapterHierarchicalBayes


open scoped BigOperators


variable {A B : Type*} [Fintype A] [Fintype B]

theorem BookProof.ChapterHierarchicalBayes.outerPosterior_sum_one (outer : A → ℝ) (inner : A → B → ℝ)
    (likelihood : A → B → ℝ)
    (hEvidence : 0 < hierEvidence outer inner likelihood) :
    ∑ a, outerPosterior outer inner likelihood a = 1 := by sorry
