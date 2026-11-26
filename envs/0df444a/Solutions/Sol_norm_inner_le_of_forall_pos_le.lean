-- Prove2me | solution 1 for norm_inner_le_of_forall_pos_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:10.593799+00:00
-- url     : https://prove2.me/submissions/4e1729f9-3d7b-476f-9163-a1d7a475168b

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
theorem _root_.solution {T : E →L[ℂ] E} {c M : ℝ} (x y : E)
    (h : ∀ s : ℝ, 0 < s →
      ‖⟪x, T y⟫_ℂ‖ ≤ M * ((s * (c * ‖x‖ ^ 2) + c * ‖y‖ ^ 2 / s) / 2)) :
    ‖⟪x, T y⟫_ℂ‖ ≤ c * M * ‖x‖ * ‖y‖ := by
  by_cases hx : x = 0
  · rw [hx, inner_zero_left, norm_zero, norm_zero, mul_zero, zero_mul]
  by_cases hy : y = 0
  · rw [hy, map_zero, inner_zero_right, norm_zero, norm_zero, mul_zero]
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hkey : (‖y‖ / ‖x‖ * (c * ‖x‖ ^ 2) + c * ‖y‖ ^ 2 / (‖y‖ / ‖x‖)) / 2 = c * ‖x‖ * ‖y‖ := by
    field_simp
    ring
  calc ‖⟪x, T y⟫_ℂ‖ ≤ M * ((‖y‖ / ‖x‖ * (c * ‖x‖ ^ 2) + c * ‖y‖ ^ 2 / (‖y‖ / ‖x‖)) / 2) :=
        h (‖y‖ / ‖x‖) (by positivity)
    _ = c * M * ‖x‖ * ‖y‖ := by rw [hkey]; ring
