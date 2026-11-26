-- Prove2me | solution 1 for re_inner_apply_self_eq_norm_cfcSqrt_sq_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:03.846131+00:00
-- url     : https://prove2.me/submissions/88f4c8e4-d293-4289-9fb0-ee9caac8307f

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

set_option autoImplicit false
open ContinuousLinearMap MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution {K : E →L[ℂ] E} (hK : 0 ≤ K) (x : E) :
    RCLike.re ⟪x, K x⟫_ℂ = ‖CFC.sqrt K x‖ ^ 2 := by
  rw [inner_apply_eq_inner_cfcSqrt_of_nonneg hK, inner_self_eq_norm_sq]
