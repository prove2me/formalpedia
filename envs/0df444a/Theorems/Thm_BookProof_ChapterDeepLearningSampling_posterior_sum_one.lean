-- Prove2me | Theorems.Thm_BookProof_ChapterDeepLearningSampling_posterior_sum_one
-- name    : BookProof.ChapterDeepLearningSampling.posterior_sum_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:29:12.441955+00:00
-- url     : https://prove2.me/theorems/47e09ae3-096f-4f54-8b2d-5506b6781e3b
-- title:
--   `BookProof.ChapterDeepLearningSampling.posterior_sum_one` (seedProb : Seed → ℝ) (train : Seed → Model) (likelihood : Model → Data → ℝ) (d : Data) (hd : 0 < evidence seedProb train
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDeepLearningSampling`.
--
--   `BookProof.ChapterDeepLearningSampling.posterior_sum_one` (seedProb : Seed → ℝ) (train : Seed → Model) (likelihood : Model → Data → ℝ) (d : Data) (hd : 0 < evidence seedProb train likelihood d) : ∑ m, posterior seedProb train likelihood d m = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDeepLearningSampling.posterior_sum_one`.

-- Generated from ChapterDeepLearningSampling.lean — theorem BookProof.ChapterDeepLearningSampling.posterior_sum_one
import Mathlib
import Definitions.Def_ChapterDeepLearningSampling
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference
open BookProof.ChapterDeepLearningSampling


open scoped BigOperators


variable {Seed Model Data : Type*}
variable [Fintype Seed] [DecidableEq Model]








variable [Fintype Model]

theorem BookProof.ChapterDeepLearningSampling.posterior_sum_one (seedProb : Seed → ℝ) (train : Seed → Model)
    (likelihood : Model → Data → ℝ) (d : Data)
    (hd : 0 < evidence seedProb train likelihood d) :
    ∑ m, posterior seedProb train likelihood d m = 1 := by sorry
