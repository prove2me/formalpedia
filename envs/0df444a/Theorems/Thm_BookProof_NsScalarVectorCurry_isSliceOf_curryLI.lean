-- Prove2me | Theorems.Thm_BookProof_NsScalarVectorCurry_isSliceOf_curryLI
-- name    : BookProof.NsScalarVectorCurry.isSliceOf_curryLI
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T17:45:45.154554+00:00
-- url     : https://prove2.me/theorems/d747c3fb-7e96-45bd-8a37-23b0cbe5b92b
-- title:
--   `BookProof.NsScalarVectorCurry.isSliceOf_curryLI` (f : Lp (Lp ℂ 2 ν) 2 μ) : IsSliceOf f (curryLI f)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsScalarVectorCurry`.
--
--   `BookProof.NsScalarVectorCurry.isSliceOf_curryLI` (f : Lp (Lp ℂ 2 ν) 2 μ) : IsSliceOf f (curryLI f)
--
--   Formalization note: Lean 4 identifier `BookProof.NsScalarVectorCurry.isSliceOf_curryLI`.

-- Generated from ChapterNsScalarVectorCurry.lean — theorem BookProof.NsScalarVectorCurry.isSliceOf_curryLI
import Mathlib
import Definitions.Def_ChapterNsScalarVectorCurry
open BookProof.NsScalarVectorCurry


open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate


noncomputable section

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}

variable [SigmaFinite μ] [SigmaFinite ν]

theorem BookProof.NsScalarVectorCurry.isSliceOf_curryLI (f : Lp (Lp ℂ 2 ν) 2 μ) : IsSliceOf f (curryLI f) := by sorry
