-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianGelfandModel_exists_probabilityMeasure_of_state_inc
-- name    : BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T18:44:55.897184+00:00
-- url     : https://prove2.me/theorems/667577a0-1127-4a11-8ae8-52a6b7a9162a
-- title:
--   `BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state_inc` (hone : psi 1 = 1) : ∃ mu : Measure X, IsProbabilityMeasure mu ∧ ∀ g : C(X, ℂ), psi g = ∫ x, g x ∂mu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianGelfandModel`.
--
--   `BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state_inc` (hone : psi 1 = 1) : ∃ mu : Measure X, IsProbabilityMeasure mu ∧ ∀ g : C(X, ℂ), psi g = ∫ x, g x ∂mu
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state_inc`.
--
--   Replaces the retired node `BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state`, whose stored statement omitted the `hpos` hypothesis binder (dropped `include`).

-- Generated from ChapterAbelianGelfandModel.lean — theorem BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state_inc
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterAbelianGelfandModel
open BookProof.ChapterAbelianGelfandModel


open MeasureTheory Complex WeakDual CompactlySupported CompactlySupportedContinuousMap
open scoped ComplexOrder


open BookProof.ChapterLinftyMultiplication

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  (psi : C(X, ℂ) →ₗ[ℂ] ℂ) (hpos : ∀ g : C(X, ℂ), 0 ≤ psi (star g * g))

include hpos in

theorem BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state_inc (hone : psi 1 = 1) :
    ∃ mu : Measure X, IsProbabilityMeasure mu ∧
      ∀ g : C(X, ℂ), psi g = ∫ x, g x ∂mu := by sorry
