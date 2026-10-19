-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianClassificationList_abelian_summand_standard_model_inc
-- name    : BookProof.ChapterAbelianClassificationList.abelian_summand_standard_model_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T20:15:45.402467+00:00
-- url     : https://prove2.me/theorems/e9a2f483-49d7-4d6e-bd07-1d439952b235
-- title:
--   `BookProof.ChapterAbelianClassificationList.abelian_summand_standard_model_inc` : (IsHilbertSum ℂ (fun b : Bool => Lp ℂ 2 (mu.restrict (splitSet (atomSet mu) b))) (splitEmbed (measurab
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianClassificationList`.
--
--   `BookProof.ChapterAbelianClassificationList.abelian_summand_standard_model_inc` : (IsHilbertSum ℂ (fun b : Bool => Lp ℂ 2 (mu.restrict (splitSet (atomSet mu) b))) (splitEmbed (measurableSet_atomSet mu))) ∧ (∀ (b : Bool) (g : ℝ → ℂ) (hg : MemLp g ⊤ mu) (u : Lp ℂ 2 (mu.restrict (splitSet (atomSet mu) b))), splitEmbed (measurableSet_atomSet mu) b (multOp g (hg.restrict _) u) = multOp g hg (splitEmbed (measurableSet_atomSet mu) b u)) ∧ (∃ B : HilbertBasis (atomSet (mu.restrict (atomSet mu))) ℂ (Lp ℂ 2 (mu.restrict (atomSet mu))), ∀ (g : ℝ → ℂ) (hg : MemLp g ⊤ (mu.restrict (atomSet mu))) (a : atomSet (mu.restrict (atomSet mu))), multOp g hg (B a) = g (a : ℝ) • B a) ∧ (mu (atomSet mu)ᶜ ≠ 0 → ∃ U : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) ≃ₗᵢ[ℂ] Lp ℂ 2 (mu.restrict (atomSet mu)ᶜ), ∀ (g : ℝ → ℂ) (hg : MemLp g ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1))) (u : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))), (U (multOp g hg u) : ℝ → ℂ) =ᵐ[mu.restrict (atomSet mu)ᶜ] fun x => g (cdf (normalized (mu.restrict (atomSet mu)ᶜ)) x) * (U u : ℝ → ℂ) x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianClassificationList.abelian_summand_standard_model_inc`.
--
--   Replaces the unuploadable node `BookProof_ChapterAbelianClassificationList_abelian_summand_standard_model`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterAbelianClassificationList.lean — theorem BookProof.ChapterAbelianClassificationList.abelian_summand_standard_model_inc
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Definitions.Def_ChapterAtomicDiagonalModel
import Definitions.Def_ChapterDiffuseUnitaryModel
import Definitions.Def_ChapterLpScaleMeasure
import Mathlib
import Definitions.Def_ChapterAbelianClassificationList
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterLpRestrictSplit
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterLpRestrictSplit
open BookProof.ChapterAbelianClassificationList


noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterMeasureAtomicDiffuse BookProof.ChapterAtomicDiagonalModel
open BookProof.ChapterDiffuseUnitaryModel BookProof.ChapterLinftyMultiplication
open BookProof.ChapterLpRestrictSplit BookProof.ChapterLpScaleMeasure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
variable (nu : Measure ℝ) [IsFiniteMeasure nu] [NullSingletonClass nu]
variable (mu : Measure ℝ) [IsProbabilityMeasure mu]

theorem BookProof.ChapterAbelianClassificationList.abelian_summand_standard_model_inc :
    (IsHilbertSum ℂ (fun b : Bool => Lp ℂ 2 (mu.restrict (splitSet (atomSet mu) b)))
        (splitEmbed (measurableSet_atomSet mu))) ∧
      (∀ (b : Bool) (g : ℝ → ℂ) (hg : MemLp g ⊤ mu)
          (u : Lp ℂ 2 (mu.restrict (splitSet (atomSet mu) b))),
        splitEmbed (measurableSet_atomSet mu) b (multOp g (hg.restrict _) u)
          = multOp g hg (splitEmbed (measurableSet_atomSet mu) b u)) ∧
      (∃ B : HilbertBasis (atomSet (mu.restrict (atomSet mu))) ℂ
          (Lp ℂ 2 (mu.restrict (atomSet mu))),
        ∀ (g : ℝ → ℂ) (hg : MemLp g ⊤ (mu.restrict (atomSet mu)))
          (a : atomSet (mu.restrict (atomSet mu))),
          multOp g hg (B a) = g (a : ℝ) • B a) ∧
      (mu (atomSet mu)ᶜ ≠ 0 →
        ∃ U : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) ≃ₗᵢ[ℂ]
            Lp ℂ 2 (mu.restrict (atomSet mu)ᶜ),
          ∀ (g : ℝ → ℂ) (hg : MemLp g ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1)))
            (u : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))),
            (U (multOp g hg u) : ℝ → ℂ)
              =ᵐ[mu.restrict (atomSet mu)ᶜ] fun x =>
                g (cdf (normalized (mu.restrict (atomSet mu)ᶜ)) x) * (U u : ℝ → ℂ) x) := by sorry
