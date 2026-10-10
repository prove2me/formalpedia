-- Prove2me | Theorems.Thm_BookProof_NsScalarVectorCurry_eLpNorm_two_sq_prime
-- name    : BookProof.NsScalarVectorCurry.eLpNorm_two_sq_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:13:02.043831+00:00
-- url     : https://prove2.me/theorems/d3998259-2e39-4353-9883-068a2276ff50
-- title:
--   BookProof.NsScalarVectorCurry.eLpNorm_two_sq'
-- statement:
--   BookProof.NsScalarVectorCurry.eLpNorm_two_sq'

-- Generated from ChapterNsScalarVectorCurry.lean — theorem BookProof.NsScalarVectorCurry.eLpNorm_two_sq'
import Mathlib
import Definitions.Def_ChapterNsScalarVectorCurry
open BookProof.NsScalarVectorCurry


open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate


noncomputable section

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}

variable [SigmaFinite μ] [SigmaFinite ν]

theorem BookProof.NsScalarVectorCurry.eLpNorm_two_sq_prime {X : Type*} [MeasurableSpace X] {E : Type*} [NormedAddCommGroup E]
    (ρ : Measure X) (h : X → E) : (eLpNorm h 2 ρ) ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2 ∂ρ := by sorry
