-- Prove2me | Theorems.Thm_BookProof_NsScalarVectorCurry_isSliceOf_fibMk
-- name    : BookProof.NsScalarVectorCurry.isSliceOf_fibMk
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:12:32.323844+00:00
-- url     : https://prove2.me/theorems/ab424b3a-afbc-4a74-a37b-ad1e48131105
-- title:
--   `BookProof.NsScalarVectorCurry.isSliceOf_fibMk` (a : Lp ℂ 2 μ) (c : Lp ℂ 2 ν) : IsSliceOf (fibMk a c) (prodMk a c)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsScalarVectorCurry`.
--
--   `BookProof.NsScalarVectorCurry.isSliceOf_fibMk` (a : Lp ℂ 2 μ) (c : Lp ℂ 2 ν) : IsSliceOf (fibMk a c) (prodMk a c)
--
--   Formalization note: Lean 4 identifier `BookProof.NsScalarVectorCurry.isSliceOf_fibMk`.

-- Generated from ChapterNsScalarVectorCurry.lean — theorem BookProof.NsScalarVectorCurry.isSliceOf_fibMk
import Mathlib
import Definitions.Def_ChapterNsScalarVectorCurry
open BookProof.NsScalarVectorCurry


open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate


noncomputable section

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}

variable [SigmaFinite μ] [SigmaFinite ν]

theorem BookProof.NsScalarVectorCurry.isSliceOf_fibMk (a : Lp ℂ 2 μ) (c : Lp ℂ 2 ν) : IsSliceOf (fibMk a c) (prodMk a c) := by sorry
