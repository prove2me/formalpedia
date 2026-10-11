-- Prove2me | Theorems.Thm_BookProof_ChapterSelectingEvents_inducedPrior_sum_one
-- name    : BookProof.ChapterSelectingEvents.inducedPrior_sum_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:45:58.871633+00:00
-- url     : https://prove2.me/theorems/1bfe140c-a3ed-4b96-9003-df6b23f29906
-- title:
--   `BookProof.ChapterSelectingEvents.inducedPrior_sum_one` (seedProb : Seed → ℝ) (train : Seed → Model) (_hnonneg : ∀ s, 0 ≤ seedProb s) (hsum : ∑ s, seedProb s = 1) : ∑ m, inducedPri
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSelectingEvents`.
--
--   `BookProof.ChapterSelectingEvents.inducedPrior_sum_one` (seedProb : Seed → ℝ) (train : Seed → Model) (_hnonneg : ∀ s, 0 ≤ seedProb s) (hsum : ∑ s, seedProb s = 1) : ∑ m, inducedPrior seedProb train m = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSelectingEvents.inducedPrior_sum_one`.

-- Generated from ChapterSelectingEvents.lean — theorem BookProof.ChapterSelectingEvents.inducedPrior_sum_one
import Mathlib
import Definitions.Def_ChapterSelectingEvents
import Definitions.Def_ChapterDeepLearningSampling
open BookProof.ChapterDeepLearningSampling
open BookProof.ChapterSelectingEvents


open scoped BigOperators
open MeasureTheory ProbabilityTheory


variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {Ω Data : Type*} [MeasurableSpace Ω]
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
variable {Seed Model : Type*} [Fintype Seed] [Fintype Model] [DecidableEq Model]

theorem BookProof.ChapterSelectingEvents.inducedPrior_sum_one (seedProb : Seed → ℝ) (train : Seed → Model)
    (_hnonneg : ∀ s, 0 ≤ seedProb s) (hsum : ∑ s, seedProb s = 1) :
    ∑ m, inducedPrior seedProb train m = 1 := by sorry
