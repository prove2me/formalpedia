-- Prove2me | solution 1 for inner_apply_eq_inner_cfcSqrt_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:43:25.987276+00:00
-- url     : https://prove2.me/submissions/6a9f2ba9-619e-40e9-aa13-1845c117527f

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Operator_Crouzeix_PositiveKernelBound

set_option autoImplicit false
open ContinuousLinearMap MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution {K : E →L[ℂ] E} (hK : 0 ≤ K) (x y : E) :
    ⟪x, K y⟫_ℂ = ⟪CFC.sqrt K x, CFC.sqrt K y⟫_ℂ := by
  have hS : IsSelfAdjoint (CFC.sqrt K) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg K)
  calc ⟪x, K y⟫_ℂ = ⟪x, (CFC.sqrt K * CFC.sqrt K) y⟫_ℂ := by rw [CFC.sqrt_mul_sqrt_self K hK]
    _ = ⟪x, adjoint (CFC.sqrt K) (CFC.sqrt K y)⟫_ℂ := by rw [mul_apply_eq_comp, hS.adjoint_eq]
    _ = ⟪CFC.sqrt K x, CFC.sqrt K y⟫_ℂ := adjoint_inner_right _ _ _
