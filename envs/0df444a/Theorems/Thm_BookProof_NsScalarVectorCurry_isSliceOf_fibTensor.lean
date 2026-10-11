-- Prove2me | Theorems.Thm_BookProof_NsScalarVectorCurry_isSliceOf_fibTensor
-- name    : BookProof.NsScalarVectorCurry.isSliceOf_fibTensor
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:05:32.344562+00:00
-- url     : https://prove2.me/theorems/ba467ca6-ed67-45a9-b493-dcfc6328cbaa
-- title:
--   `BookProof.NsScalarVectorCurry.isSliceOf_fibTensor` (t : TensorProduct ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν)) : IsSliceOf (fibTensor t) (prodTensor t)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsScalarVectorCurry`.
--
--   `BookProof.NsScalarVectorCurry.isSliceOf_fibTensor` (t : TensorProduct ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν)) : IsSliceOf (fibTensor t) (prodTensor t)
--
--   Formalization note: Lean 4 identifier `BookProof.NsScalarVectorCurry.isSliceOf_fibTensor`.

-- Generated from ChapterNsScalarVectorCurry.lean — theorem BookProof.NsScalarVectorCurry.isSliceOf_fibTensor
import Mathlib
import Definitions.Def_ChapterNsScalarVectorCurry
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval
open BookProof.NsScalarVectorCurry


open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate


noncomputable section

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}

variable [SigmaFinite μ] [SigmaFinite ν]

theorem BookProof.NsScalarVectorCurry.isSliceOf_fibTensor (t : TensorProduct ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν)) :
    IsSliceOf (fibTensor t) (prodTensor t) := by sorry
