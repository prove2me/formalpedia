-- Prove2me | Theorems.Thm_BookProof_ChapterSeparableL2Model_separable_Lp_realizes_standard_type
-- name    : BookProof.ChapterSeparableL2Model.separable_Lp_realizes_standard_type
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-02T20:43:46.226213+00:00
-- url     : https://prove2.me/theorems/778644d2-ef1f-4804-842a-c7ffe18433b6
-- title:
--   `BookProof.ChapterSeparableL2Model.separable_Lp_realizes_standard_type` [SeparableSpace (Lp ℂ 2 mu)] : ∃ (Z : Type u) (_ : MeasurableSpace Z) (_ : StandardBorelSpace Z) (_ : Measur
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSeparableL2Model`.
--
--   `BookProof.ChapterSeparableL2Model.separable_Lp_realizes_standard_type` [SeparableSpace (Lp ℂ 2 mu)] : ∃ (Z : Type u) (_ : MeasurableSpace Z) (_ : StandardBorelSpace Z) (_ : MeasurableSingletonClass Z) (Phi : Y → Z) (hPhi : Measurable Phi), ∃ _ : IsProbabilityMeasure (Measure.map Phi mu), RealizesStandardType (Measure.map Phi mu) ∧ ∃ U : Lp ℂ 2 (Measure.map Phi mu) ≃ₗᵢ[ℂ] Lp ℂ 2 mu, ∀ (g : Z → ℂ) (hg : MemLp g ⊤ (Measure.map Phi mu)) (v : Lp ℂ 2 (Measure.map Phi mu)), U (multOp g hg v) = multOp (fun y => g (Phi y)) (hg.comp_measurePreserving ⟨hPhi, rfl⟩) (U v)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSeparableL2Model.separable_Lp_realizes_standard_type`.

-- Generated from ChapterSeparableL2Model.lean — theorem BookProof.ChapterSeparableL2Model.separable_Lp_realizes_standard_type
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterAbelianCyclicModel
import Definitions.Def_ChapterAbelianDirectSum
import Definitions.Def_ChapterStandardBorelClassification
import Mathlib
import Definitions.Def_ChapterSeparableL2Model
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterWignerSymmetry
import Definitions.Def_ChapterSeparableL2Model
import Definitions.Def_ChapterWignerSymmetryInfinite
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterWignerSymmetry
open BookProof.ChapterSeparableL2Model


noncomputable section

open MeasureTheory TopologicalSpace


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterAbelianCyclicModel
open BookProof.ChapterAbelianDirectSum BookProof.ChapterLinftyMultiplication
open BookProof.ChapterStandardBorelClassification

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] (mu : Measure Y) [IsFiniteMeasure mu] [mu.WeaklyRegular]
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y]
  [BorelSpace Y] (D : Set C(Y, ℂ)) [Countable D]
universe u

variable {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] (mu : Measure Y) [IsProbabilityMeasure mu] [mu.WeaklyRegular]

theorem BookProof.ChapterSeparableL2Model.separable_Lp_realizes_standard_type [SeparableSpace (Lp ℂ 2 mu)] :
    ∃ (Z : Type u) (_ : MeasurableSpace Z) (_ : StandardBorelSpace Z)
      (_ : MeasurableSingletonClass Z) (Phi : Y → Z) (hPhi : Measurable Phi),
      ∃ _ : IsProbabilityMeasure (Measure.map Phi mu),
        RealizesStandardType (Measure.map Phi mu) ∧
        ∃ U : Lp ℂ 2 (Measure.map Phi mu) ≃ₗᵢ[ℂ] Lp ℂ 2 mu,
          ∀ (g : Z → ℂ) (hg : MemLp g ⊤ (Measure.map Phi mu))
            (v : Lp ℂ 2 (Measure.map Phi mu)),
            U (multOp g hg v)
              = multOp (fun y => g (Phi y)) (hg.comp_measurePreserving ⟨hPhi, rfl⟩) (U v) := by sorry
