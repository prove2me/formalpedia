-- Prove2me | Theorems.Thm_BookProof_ChapterDiffuseCdfModel_volume_Icc_inter_Iic
-- name    : BookProof.ChapterDiffuseCdfModel.volume_Icc_inter_Iic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T14:00:28.381752+00:00
-- url     : https://prove2.me/theorems/2f51f9ff-f9e6-480d-9f68-807eba7bd08f
-- title:
--   `BookProof.ChapterDiffuseCdfModel.volume_Icc_inter_Iic` {t : ℝ} (ht1 : t ≤ 1) : (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic t) = ENNReal.ofReal t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDiffuseCdfModel`.
--
--   `BookProof.ChapterDiffuseCdfModel.volume_Icc_inter_Iic` {t : ℝ} (ht1 : t ≤ 1) : (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic t) = ENNReal.ofReal t
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDiffuseCdfModel.volume_Icc_inter_Iic`.

-- Generated from ChapterDiffuseCdfModel.lean — theorem BookProof.ChapterDiffuseCdfModel.volume_Icc_inter_Iic
import Mathlib
import Definitions.Def_ChapterDiffuseCdfModel
open BookProof.ChapterDiffuseCdfModel


noncomputable section

open MeasureTheory ProbabilityTheory Filter


variable (mu : Measure ℝ)

theorem BookProof.ChapterDiffuseCdfModel.volume_Icc_inter_Iic {t : ℝ} (ht1 : t ≤ 1) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic t) = ENNReal.ofReal t := by sorry
