-- Prove2me | Theorems.Thm_BookProof_ChapterUniformPriorPosterior_uniform_binary_evidence
-- name    : BookProof.ChapterUniformPriorPosterior.uniform_binary_evidence
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:38:42.124338+00:00
-- url     : https://prove2.me/theorems/6d59853a-88be-4179-ad11-dda0e1bf71a3
-- title:
--   `BookProof.ChapterUniformPriorPosterior.uniform_binary_evidence` (q : Hyp → ℝ) (hq_sum : ∑ x, q x = 1) (c : ℝ) : BookProof.ChapterBayesInference.evidence (fun _ : Hyp => c) (binary
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUniformPriorPosterior`.
--
--   `BookProof.ChapterUniformPriorPosterior.uniform_binary_evidence` (q : Hyp → ℝ) (hq_sum : ∑ x, q x = 1) (c : ℝ) : BookProof.ChapterBayesInference.evidence (fun _ : Hyp => c) (binaryLikelihood q) true = c
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUniformPriorPosterior.uniform_binary_evidence`.

-- Generated from ChapterUniformPriorPosterior.lean — theorem BookProof.ChapterUniformPriorPosterior.uniform_binary_evidence
import Mathlib
import Definitions.Def_ChapterUniformPriorPosterior
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference
open BookProof.ChapterUniformPriorPosterior


open scoped BigOperators


variable {Hyp : Type*} [Fintype Hyp] [DecidableEq Hyp]

theorem BookProof.ChapterUniformPriorPosterior.uniform_binary_evidence (q : Hyp → ℝ) (hq_sum : ∑ x, q x = 1)
    (c : ℝ) :
    BookProof.ChapterBayesInference.evidence (fun _ : Hyp => c)
      (binaryLikelihood q) true = c := by sorry
