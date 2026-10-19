-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianCyclicModel_cyclic_representation_multiplication_model_inc
-- name    : BookProof.ChapterAbelianCyclicModel.cyclic_representation_multiplication_model_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T18:44:51.075926+00:00
-- url     : https://prove2.me/theorems/d6b1dfe8-cfd3-4cab-a5b8-71e7d6c9d9b4
-- title:
--   `BookProof.ChapterAbelianCyclicModel.cyclic_representation_multiplication_model_inc` (hxi : ‖xi‖ = 1) : ∃ (mu : Measure X) (_ : IsProbabilityMeasure mu) (U : Lp ℂ 2 mu ≃ₗᵢ[ℂ] H),...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianCyclicModel`.
--
--   `BookProof.ChapterAbelianCyclicModel.cyclic_representation_multiplication_model_inc` (hxi : ‖xi‖ = 1) : ∃ (mu : Measure X) (_ : IsProbabilityMeasure mu) (U : Lp ℂ 2 mu ≃ₗᵢ[ℂ] H), (∀ (g : C(X, ℂ)) (u : Lp ℂ 2 mu), U (mulRep mu g u) = pi g (U u)) ∧ (∀ (g : C(X, ℂ)) (v : H), U.symm (pi g v) = mulRep mu g (U.symm v))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianCyclicModel.cyclic_representation_multiplication_model_inc`.
--
--   Replaces the retired node `BookProof.ChapterAbelianCyclicModel.cyclic_representation_multiplication_model`, whose stored statement omitted the `hcyc` hypothesis binder (dropped `include`).

-- Generated from ChapterAbelianCyclicModel.lean — theorem BookProof.ChapterAbelianCyclicModel.cyclic_representation_multiplication_model_inc
import Definitions.Def_ChapterAbelianGelfandModel
import Mathlib
import Definitions.Def_ChapterAbelianCyclicModel
open BookProof.ChapterAbelianCyclicModel


open MeasureTheory Complex WeakDual
open scoped ComplexOrder


open BookProof.ChapterAbelianGelfandModel


variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H)

variable (hcyc : DenseRange (repVec pi xi))

include hcyc in

theorem BookProof.ChapterAbelianCyclicModel.cyclic_representation_multiplication_model_inc (hxi : ‖xi‖ = 1) :
    ∃ (mu : Measure X) (_ : IsProbabilityMeasure mu) (U : Lp ℂ 2 mu ≃ₗᵢ[ℂ] H),
      (∀ (g : C(X, ℂ)) (u : Lp ℂ 2 mu), U (mulRep mu g u) = pi g (U u)) ∧
      (∀ (g : C(X, ℂ)) (v : H), U.symm (pi g v) = mulRep mu g (U.symm v)) := by sorry
