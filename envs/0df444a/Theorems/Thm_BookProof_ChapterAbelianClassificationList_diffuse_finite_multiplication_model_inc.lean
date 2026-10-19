-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianClassificationList_diffuse_finite_multiplication_model_inc
-- name    : BookProof.ChapterAbelianClassificationList.diffuse_finite_multiplication_model_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T20:15:32.80541+00:00
-- url     : https://prove2.me/theorems/428a5e6a-d19b-47f3-b23f-d5994cce98d5
-- title:
--   `BookProof.ChapterAbelianClassificationList.diffuse_finite_multiplication_model_inc` (hne : nu Set.univ ≠ 0) : ∃ U : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) ≃ₗᵢ[ℂ] Lp ℂ 2...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianClassificationList`.
--
--   `BookProof.ChapterAbelianClassificationList.diffuse_finite_multiplication_model_inc` (hne : nu Set.univ ≠ 0) : ∃ U : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) ≃ₗᵢ[ℂ] Lp ℂ 2 nu, ∀ (g : ℝ → ℂ) (hg : MemLp g ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1))) (u : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))), (U (multOp g hg u) : ℝ → ℂ) =ᵐ[nu] fun x => g (cdf (normalized nu) x) * (U u : ℝ → ℂ) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianClassificationList.diffuse_finite_multiplication_model_inc`.
--
--   Replaces the unuploadable node `BookProof_ChapterAbelianClassificationList_diffuse_finite_multiplication_model`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterAbelianClassificationList.lean — theorem BookProof.ChapterAbelianClassificationList.diffuse_finite_multiplication_model_inc
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Definitions.Def_ChapterAtomicDiagonalModel
import Definitions.Def_ChapterDiffuseUnitaryModel
import Definitions.Def_ChapterLpRestrictSplit
import Mathlib
import Definitions.Def_ChapterAbelianClassificationList
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterLpScaleMeasure
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterLpScaleMeasure
open BookProof.ChapterAbelianClassificationList


noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterMeasureAtomicDiffuse BookProof.ChapterAtomicDiagonalModel
open BookProof.ChapterDiffuseUnitaryModel BookProof.ChapterLinftyMultiplication
open BookProof.ChapterLpRestrictSplit BookProof.ChapterLpScaleMeasure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
variable (nu : Measure ℝ) [IsFiniteMeasure nu] [NullSingletonClass nu]

theorem BookProof.ChapterAbelianClassificationList.diffuse_finite_multiplication_model_inc (hne : nu Set.univ ≠ 0) :
    ∃ U : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) ≃ₗᵢ[ℂ] Lp ℂ 2 nu,
      ∀ (g : ℝ → ℂ) (hg : MemLp g ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1)))
        (u : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))),
        (U (multOp g hg u) : ℝ → ℂ)
          =ᵐ[nu] fun x => g (cdf (normalized nu) x) * (U u : ℝ → ℂ) x := by sorry
