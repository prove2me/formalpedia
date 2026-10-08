-- Prove2me | Theorems.Thm_BookProof_ChapterDiffuseUnitaryModel_memLp_top_comp_cdf
-- name    : BookProof.ChapterDiffuseUnitaryModel.memLp_top_comp_cdf
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:56:34.552058+00:00
-- url     : https://prove2.me/theorems/2d4dc7af-957d-42f6-b8da-8189fe78d197
-- title:
--   `BookProof.ChapterDiffuseUnitaryModel.memLp_top_comp_cdf` {g : ℝ → ℂ} (hg : MemLp g ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1))) : MemLp (fun x => g (cdf mu x)) ⊤ mu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDiffuseUnitaryModel`.
--
--   `BookProof.ChapterDiffuseUnitaryModel.memLp_top_comp_cdf` {g : ℝ → ℂ} (hg : MemLp g ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1))) : MemLp (fun x => g (cdf mu x)) ⊤ mu
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDiffuseUnitaryModel.memLp_top_comp_cdf`.

-- Generated from ChapterDiffuseUnitaryModel.lean — theorem BookProof.ChapterDiffuseUnitaryModel.memLp_top_comp_cdf
import Definitions.Def_ChapterDiffuseCdfModel
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterDiffuseUnitaryModel
open BookProof.ChapterDiffuseUnitaryModel


noncomputable section

open MeasureTheory ProbabilityTheory Filter


open BookProof.ChapterDiffuseCdfModel BookProof.ChapterLinftyMultiplication

variable (mu : Measure ℝ) [IsProbabilityMeasure mu] [NullSingletonClass mu]

theorem BookProof.ChapterDiffuseUnitaryModel.memLp_top_comp_cdf {g : ℝ → ℂ}
    (hg : MemLp g ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    MemLp (fun x => g (cdf mu x)) ⊤ mu := by sorry
