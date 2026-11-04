-- Prove2me | Theorems.Thm_BookProof_ChapterStandardBorelClassification_spectral_multiplication_model_classified
-- name    : BookProof.ChapterStandardBorelClassification.spectral_multiplication_model_classified
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T09:49:30.481577+00:00
-- url     : https://prove2.me/theorems/1d057784-7b48-46b1-939f-851fe18b41e7
-- title:
--   `BookProof.ChapterStandardBorelClassification.spectral_multiplication_model_classified` (T : H →L[ℂ] H) (hT : IsStarNormal T) : ∃ (S : Set H) (mu : S → Measure (spectrum ℂ T)) (V :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStandardBorelClassification`.
--
--   `BookProof.ChapterStandardBorelClassification.spectral_multiplication_model_classified` (T : H →L[ℂ] H) (hT : IsStarNormal T) : ∃ (S : Set H) (mu : S → Measure (spectrum ℂ T)) (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] H), (∀ x : S, IsProbabilityMeasure (mu x)) ∧ IsHilbertSum ℂ (fun x : S => Lp ℂ 2 (mu x)) V ∧ (∀ (x : S) (u : Lp ℂ 2 (mu x)), V x (mulRep (mu x) (coordFn T) u) = T (V x u)) ∧ (∀ x : S, ∃ _ : IsProbabilityMeasure (mu x), RealizesStandardType (mu x))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStandardBorelClassification.spectral_multiplication_model_classified`.

-- Generated from ChapterStandardBorelClassification.lean — theorem BookProof.ChapterStandardBorelClassification.spectral_multiplication_model_classified
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Definitions.Def_ChapterAtomicDiagonalModel
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterAbelianClassificationList
import Mathlib
import Definitions.Def_ChapterStandardBorelClassification
import Definitions.Def_ChapterSeparableL2Model
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
open BookProof.ChapterStandardBorelClassification


noncomputable section

open MeasureTheory


open BookProof.ChapterMeasureAtomicDiffuse BookProof.ChapterAtomicDiagonalModel
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterAbelianClassificationList
open BookProof.ChapterAbelianGelfandModel
open BookProof.ChapterSpectralMultiplication

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (e : X ≃ᵐ Y)
  (mu : Measure X)
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  (mu : Measure X) [IsProbabilityMeasure mu]
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
  [TopologicalSpace.MetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.ChapterStandardBorelClassification.spectral_multiplication_model_classified (T : H →L[ℂ] H) (hT : IsStarNormal T) :
    ∃ (S : Set H) (mu : S → Measure (spectrum ℂ T))
      (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] H),
      (∀ x : S, IsProbabilityMeasure (mu x)) ∧
      IsHilbertSum ℂ (fun x : S => Lp ℂ 2 (mu x)) V ∧
      (∀ (x : S) (u : Lp ℂ 2 (mu x)),
        V x (mulRep (mu x) (coordFn T) u) = T (V x u)) ∧
      (∀ x : S, ∃ _ : IsProbabilityMeasure (mu x), RealizesStandardType (mu x)) := by sorry
