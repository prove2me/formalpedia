-- Prove2me | Theorems.Thm_BookProof_NsScalarVectorCurry_eLpNorm_two_sq
-- name    : BookProof.NsScalarVectorCurry.eLpNorm_two_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:12:27.320663+00:00
-- url     : https://prove2.me/theorems/218f45bc-3812-4054-8130-10d851f1306b
-- title:
--   `BookProof.NsScalarVectorCurry.eLpNorm_two_sq` {X : Type*} [MeasurableSpace X] {E : Type*} [NormedAddCommGroup E] (ρ : Measure X) (h : X → E) : (eLpNorm h 2 ρ) ^ 2 = ∫⁻ x, ‖h x‖ₑ ^
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsScalarVectorCurry`.
--
--   `BookProof.NsScalarVectorCurry.eLpNorm_two_sq` {X : Type*} [MeasurableSpace X] {E : Type*} [NormedAddCommGroup E] (ρ : Measure X) (h : X → E) : (eLpNorm h 2 ρ) ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) ∂ρ
--
--   Formalization note: Lean 4 identifier `BookProof.NsScalarVectorCurry.eLpNorm_two_sq`.

-- Generated from ChapterNsScalarVectorCurry.lean — theorem BookProof.NsScalarVectorCurry.eLpNorm_two_sq
import Mathlib
import Definitions.Def_ChapterNsScalarVectorCurry
open BookProof.NsScalarVectorCurry


open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate


noncomputable section

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}

variable [SigmaFinite μ] [SigmaFinite ν]

theorem BookProof.NsScalarVectorCurry.eLpNorm_two_sq {X : Type*} [MeasurableSpace X] {E : Type*} [NormedAddCommGroup E]
    (ρ : Measure X) (h : X → E) : (eLpNorm h 2 ρ) ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) ∂ρ := by sorry
