-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianGelfandModel_inner_oneVec_mulRep
-- name    : BookProof.ChapterAbelianGelfandModel.inner_oneVec_mulRep
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:19:57.384979+00:00
-- url     : https://prove2.me/theorems/6bab7637-b997-4b94-8ded-0a7e083feeb5
-- title:
--   `BookProof.ChapterAbelianGelfandModel.inner_oneVec_mulRep` [IsFiniteMeasure mu] (f : C(X, ℂ)) : inner ℂ (oneVec mu) (mulRep mu f (oneVec mu)) = ∫ x, f x ∂mu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianGelfandModel`.
--
--   `BookProof.ChapterAbelianGelfandModel.inner_oneVec_mulRep` [IsFiniteMeasure mu] (f : C(X, ℂ)) : inner ℂ (oneVec mu) (mulRep mu f (oneVec mu)) = ∫ x, f x ∂mu
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianGelfandModel.inner_oneVec_mulRep`.

-- Generated from ChapterAbelianGelfandModel.lean — theorem BookProof.ChapterAbelianGelfandModel.inner_oneVec_mulRep
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
variable {X : Type*} [MeasurableSpace X] (mu : Measure X)
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (mu : Measure X)

theorem BookProof.ChapterAbelianGelfandModel.inner_oneVec_mulRep [IsFiniteMeasure mu] (f : C(X, ℂ)) :
    inner ℂ (oneVec mu) (mulRep mu f (oneVec mu)) = ∫ x, f x ∂mu := by sorry
