-- Prove2me | solution 1 for resolvent_smul_one_eq_inv_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:04:46.805264+00:00
-- url     : https://prove2.me/submissions/6c0c0254-aa97-473f-865d-dda70dc0aab0

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy

set_option autoImplicit false
open Complex Filter MeasureTheory Metric Set spectrum
open scoped InnerProductSpace Interval Pointwise Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
omit [CompleteSpace E]
theorem _root_.solution
    [Nontrivial E] (c z : ℂ) (hz : z ≠ c) :
    resolvent (c • (1 : E →L[ℂ] E)) z =
      (z - c)⁻¹ • (1 : E →L[ℂ] E) := by
  have hzc : z - c ≠ 0 := sub_ne_zero.mpr hz
  have hunit : IsUnit ((z - c) • (1 : E →L[ℂ] E)) :=
    IsUnit.smul (Units.mk0 (z - c) hzc) isUnit_one
  unfold resolvent
  rw [Algebra.algebraMap_eq_smul_one, ← sub_smul]
  rw [← mul_one (Ring.inverse ((z - c) • (1 : E →L[ℂ] E)))]
  apply (Ring.inverse_mul_eq_iff_eq_mul
    ((z - c) • (1 : E →L[ℂ] E)) 1
    ((z - c)⁻¹ • (1 : E →L[ℂ] E)) hunit).2
  rw [smul_mul_smul_comm, mul_inv_cancel₀ hzc, one_smul, one_mul]
