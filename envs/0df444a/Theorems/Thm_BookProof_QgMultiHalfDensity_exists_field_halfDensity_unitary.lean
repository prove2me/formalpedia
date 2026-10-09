-- Prove2me | Theorems.Thm_BookProof_QgMultiHalfDensity_exists_field_halfDensity_unitary
-- name    : BookProof.QgMultiHalfDensity.exists_field_halfDensity_unitary
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:38:45.060331+00:00
-- url     : https://prove2.me/theorems/3b2240d5-cb08-48f6-881c-9b932fd2452e
-- title:
--   `BookProof.QgMultiHalfDensity.exists_field_halfDensity_unitary` (n : ℕ) : ∃ _W : Lp ℂ 2 (BookProof.ScalaronDensitized.physMeasure.prod (volume : Measure (Fin n → ℝ))) ≃ₗᵢ[ℂ] Lp ℂ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgMultiHalfDensity`.
--
--   `BookProof.QgMultiHalfDensity.exists_field_halfDensity_unitary` (n : ℕ) : ∃ _W : Lp ℂ 2 (BookProof.ScalaronDensitized.physMeasure.prod (volume : Measure (Fin n → ℝ))) ≃ₗᵢ[ℂ] Lp ℂ 2 (qgSrcMeasure.prod (volume : Measure (Fin n → ℝ))), True
--
--   Formalization note: Lean 4 identifier `BookProof.QgMultiHalfDensity.exists_field_halfDensity_unitary`.

-- Generated from ChapterQgMultiHalfDensity.lean — theorem BookProof.QgMultiHalfDensity.exists_field_halfDensity_unitary
import Definitions.Def_ChapterNavierStokesFockContinuum
import Mathlib
import Definitions.Def_ChapterQgMultiHalfDensity
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterScalaronDensitizedTransfer
open BookProof.QuantumGravityHalfDensity
open BookProof.ScalaronDensitized
open BookProof.QgMultiHalfDensity



open MeasureTheory Set
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.QuantumGravityHalfDensity

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {mu : Measure X} {nu : Measure Y} {Phi : X → Y} {Psi : Y → X}
variable {g : Y → ℝ}
variable {X : Type*} [MeasurableSpace X] (mu : Measure X)
variable [SFinite mu]

theorem BookProof.QgMultiHalfDensity.exists_field_halfDensity_unitary (n : ℕ) :
    ∃ _W : Lp ℂ 2 (BookProof.ScalaronDensitized.physMeasure.prod
        (volume : Measure (Fin n → ℝ)))
      ≃ₗᵢ[ℂ] Lp ℂ 2 (qgSrcMeasure.prod (volume : Measure (Fin n → ℝ))), True := by sorry
