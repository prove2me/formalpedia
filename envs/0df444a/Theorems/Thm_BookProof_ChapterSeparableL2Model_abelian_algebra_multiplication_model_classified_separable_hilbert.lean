-- Prove2me | Theorems.Thm_BookProof_ChapterSeparableL2Model_abelian_algebra_multiplication_model_classified_separable_hilbert
-- name    : BookProof.ChapterSeparableL2Model.abelian_algebra_multiplication_model_classified_separable_hilbert
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-02T20:42:53.535703+00:00
-- url     : https://prove2.me/theorems/142ca635-d5f2-415f-a266-823c3db8630d
-- title:
--   `BookProof.ChapterSeparableL2Model.abelian_algebra_multiplication_model_classified_separable_hilbert` [TopologicalSpace.SeparableSpace H] (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : ∃ (S : Set
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSeparableL2Model`.
--
--   `BookProof.ChapterSeparableL2Model.abelian_algebra_multiplication_model_classified_separable_hilbert` [TopologicalSpace.SeparableSpace H] (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : ∃ (S : Set H) (mu : S → Measure (characterSpace ℂ A)) (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] H), S.Countable ∧ (∀ x : S, IsProbabilityMeasure (mu x)) ∧ IsHilbertSum ℂ (fun x : S => Lp ℂ 2 (mu x)) V ∧ (∀ (x : S) (a : A) (u : Lp ℂ 2 (mu x)), V x (mulRep (mu x) (gelfandModel A a) u) = rho a (V x u)) ∧ (∀ x : S, ∃ (Z : Type v) (_ : MeasurableSpace Z) (_ : StandardBorelSpace Z) (_ : MeasurableSingletonClass Z) (Phi : characterSpace ℂ A → Z) (hPhi : Measurable Phi), ∃ _ : IsProbabilityMeasure (Measure.map Phi (mu x)), RealizesStandardType (Measure.map Phi (mu x)) ∧ ∃ U : Lp ℂ 2 (Measure.map Phi (mu x)) ≃ₗᵢ[ℂ] Lp ℂ 2 (mu x), ∀ (g : Z → ℂ) (hg : MemLp g ⊤ (Measure.map Phi (mu x))) (v : Lp ℂ 2 (Measure.map Phi (mu x))), U (multOp g hg v) = multOp (fun y => g (Phi y)) (hg.comp_measurePreserving ⟨hPhi, rfl⟩) (U v))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSeparableL2Model.abelian_algebra_multiplication_model_classified_separable_hilbert`.

-- Generated from ChapterSeparableL2Model.lean — theorem BookProof.ChapterSeparableL2Model.abelian_algebra_multiplication_model_classified_separable_hilbert
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterAbelianCyclicModel
import Definitions.Def_ChapterAbelianDirectSum
import Definitions.Def_ChapterStandardBorelClassification
import Mathlib
import Definitions.Def_ChapterSeparableL2Model
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterSeparableL2Model
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterSeparableL2Model


noncomputable section

open MeasureTheory TopologicalSpace


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterAbelianCyclicModel
open BookProof.ChapterAbelianDirectSum BookProof.ChapterLinftyMultiplication
open BookProof.ChapterStandardBorelClassification

universe u
-- `characterSpace` is Mathlib's `WeakDual.characterSpace` (a Def that uses it
-- opens `WeakDual`); the stub referenced it bare.
open WeakDual

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] (mu : Measure Y) [IsFiniteMeasure mu] [mu.WeaklyRegular]
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y]
  [BorelSpace Y] (D : Set C(Y, ℂ)) [Countable D]
variable {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] (mu : Measure Y) [IsProbabilityMeasure mu] [mu.WeaklyRegular]
variable {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
universe v

variable {A : Type v} [CommCStarAlgebra A]

theorem BookProof.ChapterSeparableL2Model.abelian_algebra_multiplication_model_classified_separable_hilbert
    [TopologicalSpace.SeparableSpace H] (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    ∃ (S : Set H) (mu : S → Measure (characterSpace ℂ A))
      (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] H),
      S.Countable ∧
      (∀ x : S, IsProbabilityMeasure (mu x)) ∧
      IsHilbertSum ℂ (fun x : S => Lp ℂ 2 (mu x)) V ∧
      (∀ (x : S) (a : A) (u : Lp ℂ 2 (mu x)),
        V x (mulRep (mu x) (gelfandModel A a) u) = rho a (V x u)) ∧
      (∀ x : S, ∃ (Z : Type v) (_ : MeasurableSpace Z) (_ : StandardBorelSpace Z)
        (_ : MeasurableSingletonClass Z) (Phi : characterSpace ℂ A → Z)
        (hPhi : Measurable Phi),
        ∃ _ : IsProbabilityMeasure (Measure.map Phi (mu x)),
          RealizesStandardType (Measure.map Phi (mu x)) ∧
          ∃ U : Lp ℂ 2 (Measure.map Phi (mu x)) ≃ₗᵢ[ℂ] Lp ℂ 2 (mu x),
            ∀ (g : Z → ℂ) (hg : MemLp g ⊤ (Measure.map Phi (mu x)))
              (v : Lp ℂ 2 (Measure.map Phi (mu x))),
              U (multOp g hg v)
                = multOp (fun y => g (Phi y)) (hg.comp_measurePreserving ⟨hPhi, rfl⟩) (U v)) := by sorry
