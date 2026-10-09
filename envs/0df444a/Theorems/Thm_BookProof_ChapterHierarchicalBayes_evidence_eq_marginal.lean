-- Prove2me | Theorems.Thm_BookProof_ChapterHierarchicalBayes_evidence_eq_marginal
-- name    : BookProof.ChapterHierarchicalBayes.evidence_eq_marginal
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:13:03.139992+00:00
-- url     : https://prove2.me/theorems/1d5cf4e6-9415-4708-89e4-61cb81fc9a5f
-- title:
--   `BookProof.ChapterHierarchicalBayes.evidence_eq_marginal` (outer : A → ℝ) (inner : A → B → ℝ) (likelihood : A → B → ℝ) : hierEvidence outer inner likelihood = ∑ a, outer a * margin
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHierarchicalBayes`.
--
--   `BookProof.ChapterHierarchicalBayes.evidence_eq_marginal` (outer : A → ℝ) (inner : A → B → ℝ) (likelihood : A → B → ℝ) : hierEvidence outer inner likelihood = ∑ a, outer a * marginalLikelihood inner likelihood a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterHierarchicalBayes.evidence_eq_marginal`.

-- Generated from ChapterHierarchicalBayes.lean — theorem BookProof.ChapterHierarchicalBayes.evidence_eq_marginal
import Mathlib
import Definitions.Def_ChapterHierarchicalBayes
open BookProof.ChapterHierarchicalBayes


open scoped BigOperators


variable {A B : Type*} [Fintype A] [Fintype B]

theorem BookProof.ChapterHierarchicalBayes.evidence_eq_marginal (outer : A → ℝ) (inner : A → B → ℝ)
    (likelihood : A → B → ℝ) :
    hierEvidence outer inner likelihood =
      ∑ a, outer a * marginalLikelihood inner likelihood a := by sorry
