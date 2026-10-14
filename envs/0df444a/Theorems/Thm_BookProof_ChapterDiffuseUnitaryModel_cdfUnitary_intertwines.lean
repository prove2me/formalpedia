-- Prove2me | Theorems.Thm_BookProof_ChapterDiffuseUnitaryModel_cdfUnitary_intertwines
-- name    : BookProof.ChapterDiffuseUnitaryModel.cdfUnitary_intertwines
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:16:38.720272+00:00
-- url     : https://prove2.me/theorems/9e95846d-acc8-47eb-a6ab-46b49a8f4898
-- title:
--   `BookProof.ChapterDiffuseUnitaryModel.cdfUnitary_intertwines` {g : ℝ → ℂ} (hg : MemLp g ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1))) (u : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDiffuseUnitaryModel`.
--
--   `BookProof.ChapterDiffuseUnitaryModel.cdfUnitary_intertwines` {g : ℝ → ℂ} (hg : MemLp g ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1))) (u : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) : cdfUnitary mu (multOp g hg u) = multOp (fun x => g (cdf mu x)) (memLp_top_comp_cdf mu hg) (cdfUnitary mu u)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDiffuseUnitaryModel.cdfUnitary_intertwines`.

-- Generated from ChapterDiffuseUnitaryModel.lean — theorem BookProof.ChapterDiffuseUnitaryModel.cdfUnitary_intertwines
import Definitions.Def_ChapterDiffuseCdfModel
import Mathlib
import Definitions.Def_ChapterDiffuseUnitaryModel
import Definitions.Def_ChapterLinftyMultiplication
import Theorems.Thm_BookProof_ChapterDiffuseUnitaryModel_memLp_top_comp_cdf
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterDiffuseUnitaryModel


noncomputable section

open MeasureTheory ProbabilityTheory Filter


open BookProof.ChapterDiffuseCdfModel BookProof.ChapterLinftyMultiplication

variable (mu : Measure ℝ) [IsProbabilityMeasure mu] [NullSingletonClass mu]

theorem BookProof.ChapterDiffuseUnitaryModel.cdfUnitary_intertwines {g : ℝ → ℂ}
    (hg : MemLp g ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (u : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    cdfUnitary mu (multOp g hg u) =
      multOp (fun x => g (cdf mu x)) (memLp_top_comp_cdf mu hg) (cdfUnitary mu u) := by sorry
