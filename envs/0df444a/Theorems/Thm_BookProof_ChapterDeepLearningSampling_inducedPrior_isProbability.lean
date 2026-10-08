-- Prove2me | Theorems.Thm_BookProof_ChapterDeepLearningSampling_inducedPrior_isProbability
-- name    : BookProof.ChapterDeepLearningSampling.inducedPrior_isProbability
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:29:17.248544+00:00
-- url     : https://prove2.me/theorems/f250a9a2-768a-4ca6-a55f-05652be66592
-- title:
--   `BookProof.ChapterDeepLearningSampling.inducedPrior_isProbability` [Fintype Model] (seedProb : Seed → ℝ) (train : Seed → Model) (hnonneg : ∀ s, 0 ≤ seedProb s) (hsum : ∑ s, seedPro
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDeepLearningSampling`.
--
--   `BookProof.ChapterDeepLearningSampling.inducedPrior_isProbability` [Fintype Model] (seedProb : Seed → ℝ) (train : Seed → Model) (hnonneg : ∀ s, 0 ≤ seedProb s) (hsum : ∑ s, seedProb s = 1) : (∀ m, 0 ≤ inducedPrior seedProb train m) ∧ ∑ m, inducedPrior seedProb train m = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDeepLearningSampling.inducedPrior_isProbability`.

-- Generated from ChapterDeepLearningSampling.lean — theorem BookProof.ChapterDeepLearningSampling.inducedPrior_isProbability
import Mathlib
import Definitions.Def_ChapterDeepLearningSampling
open BookProof.ChapterDeepLearningSampling


open scoped BigOperators


variable {Seed Model Data : Type*}
variable [Fintype Seed] [DecidableEq Model]

theorem BookProof.ChapterDeepLearningSampling.inducedPrior_isProbability [Fintype Model]
    (seedProb : Seed → ℝ) (train : Seed → Model)
    (hnonneg : ∀ s, 0 ≤ seedProb s) (hsum : ∑ s, seedProb s = 1) :
    (∀ m, 0 ≤ inducedPrior seedProb train m) ∧
      ∑ m, inducedPrior seedProb train m = 1 := by sorry
