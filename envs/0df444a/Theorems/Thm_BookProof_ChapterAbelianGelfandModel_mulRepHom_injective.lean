-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianGelfandModel_mulRepHom_injective
-- name    : BookProof.ChapterAbelianGelfandModel.mulRepHom_injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:20:11.96769+00:00
-- url     : https://prove2.me/theorems/f3d4bf12-55aa-4c10-a1af-22a61b2f47e3
-- title:
--   `BookProof.ChapterAbelianGelfandModel.mulRepHom_injective` [IsFiniteMeasure mu] [mu.IsOpenPosMeasure] [T2Space X] : Function.Injective (mulRepHom mu)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianGelfandModel`.
--
--   `BookProof.ChapterAbelianGelfandModel.mulRepHom_injective` [IsFiniteMeasure mu] [mu.IsOpenPosMeasure] [T2Space X] : Function.Injective (mulRepHom mu)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianGelfandModel.mulRepHom_injective`.

-- Generated from ChapterAbelianGelfandModel.lean — theorem BookProof.ChapterAbelianGelfandModel.mulRepHom_injective
import Mathlib
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication
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
variable {X : Type*} [MeasurableSpace X] (mu : Measure X)
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (mu : Measure X)

theorem BookProof.ChapterAbelianGelfandModel.mulRepHom_injective [IsFiniteMeasure mu] [mu.IsOpenPosMeasure] [T2Space X] :
    Function.Injective (mulRepHom mu) := by sorry
