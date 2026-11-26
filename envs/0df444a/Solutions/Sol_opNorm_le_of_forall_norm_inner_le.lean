-- Prove2me | solution 1 for opNorm_le_of_forall_norm_inner_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:09.41178+00:00
-- url     : https://prove2.me/submissions/a9235757-1da6-42ca-bb4d-a6ceacc51fdc

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
omit [CompleteSpace E]
theorem _root_.solution {T : E →L[ℂ] E} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x y : E, ‖⟪x, T y⟫_ℂ‖ ≤ M * ‖x‖ * ‖y‖) : ‖T‖ ≤ M := by
  refine opNorm_le_bound T hM fun y => ?_
  by_cases hy : T y = 0
  · rw [hy, norm_zero]; positivity
  · have hpos : 0 < ‖T y‖ := norm_pos_iff.mpr hy
    have h1 : ‖T y‖ ^ 2 ≤ ‖⟪T y, T y⟫_ℂ‖ := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]; exact RCLike.re_le_norm _
    have h2 : ‖T y‖ * ‖T y‖ ≤ ‖T y‖ * (M * ‖y‖) := by
      calc ‖T y‖ * ‖T y‖ = ‖T y‖ ^ 2 := (sq _).symm
        _ ≤ ‖⟪T y, T y⟫_ℂ‖ := h1
        _ ≤ M * ‖T y‖ * ‖y‖ := h (T y) y
        _ = ‖T y‖ * (M * ‖y‖) := by ring
    exact le_of_mul_le_mul_left h2 hpos
