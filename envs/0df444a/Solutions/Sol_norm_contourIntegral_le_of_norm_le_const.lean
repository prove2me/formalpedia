-- Prove2me | solution 1 for norm_contourIntegral_le_of_norm_le_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:44:03.248809+00:00
-- url     : https://prove2.me/submissions/f9224cbc-2f15-487f-9069-4afd76965c86

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral

set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
theorem _root_.solution {f : ℂ → F} {γ : ℝ → ℂ} {C : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) (2 * π), ‖deriv γ t • f (γ t)‖ ≤ C) :
    ‖contourIntegral f γ‖ ≤ 2 * π * C := by
  unfold contourIntegral
  calc
    ‖∫ t in (0 : ℝ)..(2 * π), deriv γ t • f (γ t)‖ ≤ C * |2 * π - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
      rw [uIoc_of_le Real.two_pi_pos.le] at ht
      exact h t (Ioc_subset_Icc_self ht)
    _ = 2 * π * C := by
      rw [sub_zero, abs_of_pos Real.two_pi_pos]
      ring
