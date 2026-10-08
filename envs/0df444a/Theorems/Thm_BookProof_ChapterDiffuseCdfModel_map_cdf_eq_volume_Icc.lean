-- Prove2me | Theorems.Thm_BookProof_ChapterDiffuseCdfModel_map_cdf_eq_volume_Icc
-- name    : BookProof.ChapterDiffuseCdfModel.map_cdf_eq_volume_Icc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:51:39.179358+00:00
-- url     : https://prove2.me/theorems/49aff7b8-3be4-4736-921e-a339bbd4b4d1
-- title:
--   `BookProof.ChapterDiffuseCdfModel.map_cdf_eq_volume_Icc` [IsProbabilityMeasure mu] [NullSingletonClass mu] : Measure.map (cdf mu) mu = volume.restrict (Set.Icc (0 : ℝ) 1)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDiffuseCdfModel`.
--
--   `BookProof.ChapterDiffuseCdfModel.map_cdf_eq_volume_Icc` [IsProbabilityMeasure mu] [NullSingletonClass mu] : Measure.map (cdf mu) mu = volume.restrict (Set.Icc (0 : ℝ) 1)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDiffuseCdfModel.map_cdf_eq_volume_Icc`.

-- Generated from ChapterDiffuseCdfModel.lean — theorem BookProof.ChapterDiffuseCdfModel.map_cdf_eq_volume_Icc
import Mathlib
import Definitions.Def_ChapterDiffuseCdfModel
open BookProof.ChapterDiffuseCdfModel


noncomputable section

open MeasureTheory ProbabilityTheory Filter


variable (mu : Measure ℝ)

theorem BookProof.ChapterDiffuseCdfModel.map_cdf_eq_volume_Icc [IsProbabilityMeasure mu] [NullSingletonClass mu] :
    Measure.map (cdf mu) mu = volume.restrict (Set.Icc (0 : ℝ) 1) := by sorry
