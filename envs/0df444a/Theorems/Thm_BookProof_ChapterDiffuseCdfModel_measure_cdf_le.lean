-- Prove2me | Theorems.Thm_BookProof_ChapterDiffuseCdfModel_measure_cdf_le
-- name    : BookProof.ChapterDiffuseCdfModel.measure_cdf_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:51:15.02596+00:00
-- url     : https://prove2.me/theorems/72c648a5-9b2e-41da-b5f3-c56ef1f8c4ac
-- title:
--   `BookProof.ChapterDiffuseCdfModel.measure_cdf_le` [IsProbabilityMeasure mu] [NullSingletonClass mu] {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : mu {x | cdf mu x ≤ t} = ENNReal.ofReal t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDiffuseCdfModel`.
--
--   `BookProof.ChapterDiffuseCdfModel.measure_cdf_le` [IsProbabilityMeasure mu] [NullSingletonClass mu] {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : mu {x | cdf mu x ≤ t} = ENNReal.ofReal t
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDiffuseCdfModel.measure_cdf_le`.

-- Generated from ChapterDiffuseCdfModel.lean — theorem BookProof.ChapterDiffuseCdfModel.measure_cdf_le
import Mathlib
import Definitions.Def_ChapterDiffuseCdfModel
open BookProof.ChapterDiffuseCdfModel


noncomputable section

open MeasureTheory ProbabilityTheory Filter


variable (mu : Measure ℝ)

theorem BookProof.ChapterDiffuseCdfModel.measure_cdf_le [IsProbabilityMeasure mu] [NullSingletonClass mu] {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) : mu {x | cdf mu x ≤ t} = ENNReal.ofReal t := by sorry
