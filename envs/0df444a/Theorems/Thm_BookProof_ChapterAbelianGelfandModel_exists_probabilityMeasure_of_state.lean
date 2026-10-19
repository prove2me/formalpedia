-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianGelfandModel_exists_probabilityMeasure_of_state
-- name    : BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state
-- status  : Disproved
-- author  : @leonardopedro
-- created : 2026-10-17T00:19:09.030986+00:00
-- url     : https://prove2.me/theorems/d6cb3b83-9447-4895-86e0-8575a0a31458
-- title:
--   `BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state` (hone : psi 1 = 1) : ∃ mu : Measure X, IsProbabilityMeasure mu ∧ ∀ g : C(X, ℂ), psi g = ∫ x, g x ∂mu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianGelfandModel`.
--
--   `BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state` (hone : psi 1 = 1) : ∃ mu : Measure X, IsProbabilityMeasure mu ∧ ∀ g : C(X, ℂ), psi g = ∫ x, g x ∂mu
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state`.

-- Generated from ChapterAbelianGelfandModel.lean — theorem BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterAbelianGelfandModel
open BookProof.ChapterAbelianGelfandModel


open MeasureTheory Complex WeakDual CompactlySupported CompactlySupportedContinuousMap
open scoped ComplexOrder


open BookProof.ChapterLinftyMultiplication

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {X : Type*} [TopologicalSpace X]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  (psi : C(X, ℂ) →ₗ[ℂ] ℂ) (hpos : ∀ g : C(X, ℂ), 0 ≤ psi (star g * g))

theorem BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state (hone : psi 1 = 1) :
    ∃ mu : Measure X, IsProbabilityMeasure mu ∧
      ∀ g : C(X, ℂ), psi g = ∫ x, g x ∂mu := by sorry
