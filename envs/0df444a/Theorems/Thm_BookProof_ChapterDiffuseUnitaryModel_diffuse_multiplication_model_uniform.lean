-- Prove2me | Theorems.Thm_BookProof_ChapterDiffuseUnitaryModel_diffuse_multiplication_model_uniform
-- name    : BookProof.ChapterDiffuseUnitaryModel.diffuse_multiplication_model_uniform
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:57:13.63527+00:00
-- url     : https://prove2.me/theorems/322df768-8fb0-4c99-abab-4037904ea824
-- title:
--   `BookProof.ChapterDiffuseUnitaryModel.diffuse_multiplication_model_uniform` : ∃ U : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) ≃ₗᵢ[ℂ] Lp ℂ 2 mu, ∀ (g : ℝ → ℂ) (hg :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDiffuseUnitaryModel`.
--
--   `BookProof.ChapterDiffuseUnitaryModel.diffuse_multiplication_model_uniform` : ∃ U : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) ≃ₗᵢ[ℂ] Lp ℂ 2 mu, ∀ (g : ℝ → ℂ) (hg : MemLp g ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1))) (u : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))), (U (multOp g hg u) : ℝ → ℂ) =ᵐ[mu] fun x => g (cdf mu x) * (U u : ℝ → ℂ) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDiffuseUnitaryModel.diffuse_multiplication_model_uniform`.

-- Generated from ChapterDiffuseUnitaryModel.lean — theorem BookProof.ChapterDiffuseUnitaryModel.diffuse_multiplication_model_uniform
import Definitions.Def_ChapterDiffuseCdfModel
import Mathlib
import Definitions.Def_ChapterDiffuseUnitaryModel
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterDiffuseUnitaryModel


noncomputable section

open MeasureTheory ProbabilityTheory Filter


open BookProof.ChapterDiffuseCdfModel BookProof.ChapterLinftyMultiplication

variable (mu : Measure ℝ) [IsProbabilityMeasure mu] [NullSingletonClass mu]

theorem BookProof.ChapterDiffuseUnitaryModel.diffuse_multiplication_model_uniform :
    ∃ U : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) ≃ₗᵢ[ℂ] Lp ℂ 2 mu,
      ∀ (g : ℝ → ℂ) (hg : MemLp g ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1)))
        (u : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))),
        (U (multOp g hg u) : ℝ → ℂ) =ᵐ[mu] fun x => g (cdf mu x) * (U u : ℝ → ℂ) x := by sorry
