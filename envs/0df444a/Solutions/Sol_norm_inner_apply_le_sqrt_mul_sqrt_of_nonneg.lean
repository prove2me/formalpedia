-- Prove2me | solution 1 for norm_inner_apply_le_sqrt_mul_sqrt_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:41.477857+00:00
-- url     : https://prove2.me/submissions/af573ba9-1cc5-4c83-94d6-b4051284c369

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Operator_Crouzeix_PositiveKernelBound
import Theorems.Thm_inner_apply_eq_inner_cfcSqrt_of_nonneg
import Theorems.Thm_re_inner_apply_self_eq_norm_cfcSqrt_sq_of_nonneg

set_option autoImplicit false
open ContinuousLinearMap MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution {K : E →L[ℂ] E} (hK : 0 ≤ K) (x y : E) :
    ‖⟪x, K y⟫_ℂ‖ ≤
      Real.sqrt (RCLike.re ⟪x, K x⟫_ℂ) * Real.sqrt (RCLike.re ⟪y, K y⟫_ℂ) := by
  rw [inner_apply_eq_inner_cfcSqrt_of_nonneg hK x y,
    re_inner_apply_self_eq_norm_cfcSqrt_sq_of_nonneg hK x,
    re_inner_apply_self_eq_norm_cfcSqrt_sq_of_nonneg hK y,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact norm_inner_le_norm _ _
