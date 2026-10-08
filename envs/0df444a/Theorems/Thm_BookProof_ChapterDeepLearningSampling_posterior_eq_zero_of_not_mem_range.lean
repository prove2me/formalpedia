-- Prove2me | Theorems.Thm_BookProof_ChapterDeepLearningSampling_posterior_eq_zero_of_not_mem_range
-- name    : BookProof.ChapterDeepLearningSampling.posterior_eq_zero_of_not_mem_range
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:29:10.487142+00:00
-- url     : https://prove2.me/theorems/8d5146bd-bf05-40ba-90af-b7d4fd5ef340
-- title:
--   `BookProof.ChapterDeepLearningSampling.posterior_eq_zero_of_not_mem_range` (seedProb : Seed → ℝ) (train : Seed → Model) (likelihood : Model → Data → ℝ) (d : Data) {m : Model} (hm :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDeepLearningSampling`.
--
--   `BookProof.ChapterDeepLearningSampling.posterior_eq_zero_of_not_mem_range` (seedProb : Seed → ℝ) (train : Seed → Model) (likelihood : Model → Data → ℝ) (d : Data) {m : Model} (hm : m ∉ Set.range train) : posterior seedProb train likelihood d m = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDeepLearningSampling.posterior_eq_zero_of_not_mem_range`.

-- Generated from ChapterDeepLearningSampling.lean — theorem BookProof.ChapterDeepLearningSampling.posterior_eq_zero_of_not_mem_range
import Mathlib
import Definitions.Def_ChapterDeepLearningSampling
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference
open BookProof.ChapterDeepLearningSampling


open scoped BigOperators


variable {Seed Model Data : Type*}
variable [Fintype Seed] [DecidableEq Model]








variable [Fintype Model]

theorem BookProof.ChapterDeepLearningSampling.posterior_eq_zero_of_not_mem_range (seedProb : Seed → ℝ)
    (train : Seed → Model) (likelihood : Model → Data → ℝ) (d : Data)
    {m : Model} (hm : m ∉ Set.range train) :
    posterior seedProb train likelihood d m = 0 := by sorry
