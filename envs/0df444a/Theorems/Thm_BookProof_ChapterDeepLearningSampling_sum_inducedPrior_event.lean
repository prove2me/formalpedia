-- Prove2me | Theorems.Thm_BookProof_ChapterDeepLearningSampling_sum_inducedPrior_event
-- name    : BookProof.ChapterDeepLearningSampling.sum_inducedPrior_event
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:28:44.656114+00:00
-- url     : https://prove2.me/theorems/16ab8d74-02e0-4fe1-bbfa-9e0e5a349da8
-- title:
--   `BookProof.ChapterDeepLearningSampling.sum_inducedPrior_event` (seedProb : Seed → ℝ) (train : Seed → Model) (A : Finset Model) : ∑ m ∈ A, inducedPrior seedProb train m = ∑ s with t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDeepLearningSampling`.
--
--   `BookProof.ChapterDeepLearningSampling.sum_inducedPrior_event` (seedProb : Seed → ℝ) (train : Seed → Model) (A : Finset Model) : ∑ m ∈ A, inducedPrior seedProb train m = ∑ s with train s ∈ A, seedProb s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDeepLearningSampling.sum_inducedPrior_event`.

-- Generated from ChapterDeepLearningSampling.lean — theorem BookProof.ChapterDeepLearningSampling.sum_inducedPrior_event
import Mathlib
import Definitions.Def_ChapterDeepLearningSampling
open BookProof.ChapterDeepLearningSampling


open scoped BigOperators


variable {Seed Model Data : Type*}
variable [Fintype Seed] [DecidableEq Model]

theorem BookProof.ChapterDeepLearningSampling.sum_inducedPrior_event
    (seedProb : Seed → ℝ) (train : Seed → Model)
    (A : Finset Model) :
    ∑ m ∈ A, inducedPrior seedProb train m = ∑ s with train s ∈ A, seedProb s := by sorry
