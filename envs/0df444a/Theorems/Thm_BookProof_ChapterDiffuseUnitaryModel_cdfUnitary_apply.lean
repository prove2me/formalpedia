-- Prove2me | Theorems.Thm_BookProof_ChapterDiffuseUnitaryModel_cdfUnitary_apply
-- name    : BookProof.ChapterDiffuseUnitaryModel.cdfUnitary_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:56:40.233754+00:00
-- url     : https://prove2.me/theorems/f8448ad7-d65f-4b30-9ef3-4e135cd2d38b
-- title:
--   `BookProof.ChapterDiffuseUnitaryModel.cdfUnitary_apply` (f : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) : cdfUnitary mu f = cdfComp mu f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDiffuseUnitaryModel`.
--
--   `BookProof.ChapterDiffuseUnitaryModel.cdfUnitary_apply` (f : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) : cdfUnitary mu f = cdfComp mu f
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDiffuseUnitaryModel.cdfUnitary_apply`.

-- Generated from ChapterDiffuseUnitaryModel.lean — theorem BookProof.ChapterDiffuseUnitaryModel.cdfUnitary_apply
import Definitions.Def_ChapterDiffuseCdfModel
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterDiffuseUnitaryModel
open BookProof.ChapterDiffuseUnitaryModel


noncomputable section

open MeasureTheory ProbabilityTheory Filter


open BookProof.ChapterDiffuseCdfModel BookProof.ChapterLinftyMultiplication

variable (mu : Measure ℝ) [IsProbabilityMeasure mu] [NullSingletonClass mu]

theorem BookProof.ChapterDiffuseUnitaryModel.cdfUnitary_apply (f : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    cdfUnitary mu f = cdfComp mu f := by sorry
