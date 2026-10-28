-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianGelfandModel_state_is_vector_state_of_multiplication
-- name    : BookProof.ChapterAbelianGelfandModel.state_is_vector_state_of_multiplication
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:20:32.723737+00:00
-- url     : https://prove2.me/theorems/cab8573a-6f90-422a-aeba-797314d7e2a1
-- title:
--   `BookProof.ChapterAbelianGelfandModel.state_is_vector_state_of_multiplication` (phi : A →ₗ[ℂ] ℂ) (hpos : ∀ a : A, 0 ≤ phi (star a * a)) (hone : phi 1 = 1) : ∃ mu : Measure (charact
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianGelfandModel`.
--
--   `BookProof.ChapterAbelianGelfandModel.state_is_vector_state_of_multiplication` (phi : A →ₗ[ℂ] ℂ) (hpos : ∀ a : A, 0 ≤ phi (star a * a)) (hone : phi 1 = 1) : ∃ mu : Measure (characterSpace ℂ A), ∃ _ : IsProbabilityMeasure mu, ‖oneVec mu‖ = 1 ∧ ∀ a : A, phi a = inner ℂ (oneVec mu) (multiplicationRep mu a (oneVec mu))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianGelfandModel.state_is_vector_state_of_multiplication`.

-- Generated from ChapterAbelianGelfandModel.lean — theorem BookProof.ChapterAbelianGelfandModel.state_is_vector_state_of_multiplication
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
variable (A : Type*) [CommCStarAlgebra A]
variable {A}

theorem BookProof.ChapterAbelianGelfandModel.state_is_vector_state_of_multiplication (phi : A →ₗ[ℂ] ℂ)
    (hpos : ∀ a : A, 0 ≤ phi (star a * a)) (hone : phi 1 = 1) :
    ∃ mu : Measure (characterSpace ℂ A), ∃ _ : IsProbabilityMeasure mu,
      ‖oneVec mu‖ = 1 ∧
      ∀ a : A, phi a = inner ℂ (oneVec mu) (multiplicationRep mu a (oneVec mu)) := by sorry
