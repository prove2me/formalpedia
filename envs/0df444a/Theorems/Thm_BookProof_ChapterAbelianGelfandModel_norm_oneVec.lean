-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianGelfandModel_norm_oneVec
-- name    : BookProof.ChapterAbelianGelfandModel.norm_oneVec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:19:58.112984+00:00
-- url     : https://prove2.me/theorems/b041989a-f0c2-493c-b3a9-a27d05c01d01
-- title:
--   `BookProof.ChapterAbelianGelfandModel.norm_oneVec` [IsProbabilityMeasure mu] : ‖oneVec mu‖ = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianGelfandModel`.
--
--   `BookProof.ChapterAbelianGelfandModel.norm_oneVec` [IsProbabilityMeasure mu] : ‖oneVec mu‖ = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianGelfandModel.norm_oneVec`.

-- Generated from ChapterAbelianGelfandModel.lean — theorem BookProof.ChapterAbelianGelfandModel.norm_oneVec
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

theorem BookProof.ChapterAbelianGelfandModel.norm_oneVec [IsProbabilityMeasure mu] : ‖oneVec mu‖ = 1 := by sorry
