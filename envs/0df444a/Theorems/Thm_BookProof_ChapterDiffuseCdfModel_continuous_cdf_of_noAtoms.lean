-- Prove2me | Theorems.Thm_BookProof_ChapterDiffuseCdfModel_continuous_cdf_of_noAtoms
-- name    : BookProof.ChapterDiffuseCdfModel.continuous_cdf_of_noAtoms
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T14:02:35.104567+00:00
-- url     : https://prove2.me/theorems/e3e84a8e-5bf3-4455-8e0d-f6301a6c0a90
-- title:
--   `BookProof.ChapterDiffuseCdfModel.continuous_cdf_of_noAtoms` [IsProbabilityMeasure mu] [NullSingletonClass mu] : Continuous (cdf mu)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDiffuseCdfModel`.
--
--   `BookProof.ChapterDiffuseCdfModel.continuous_cdf_of_noAtoms` [IsProbabilityMeasure mu] [NullSingletonClass mu] : Continuous (cdf mu)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDiffuseCdfModel.continuous_cdf_of_noAtoms`.

-- Generated from ChapterDiffuseCdfModel.lean — theorem BookProof.ChapterDiffuseCdfModel.continuous_cdf_of_noAtoms
import Mathlib
import Definitions.Def_ChapterDiffuseCdfModel
open BookProof.ChapterDiffuseCdfModel


noncomputable section

open MeasureTheory ProbabilityTheory Filter


variable (mu : Measure ℝ)

theorem BookProof.ChapterDiffuseCdfModel.continuous_cdf_of_noAtoms [IsProbabilityMeasure mu] [NullSingletonClass mu] :
    Continuous (cdf mu) := by sorry
