-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_primitive_continuousOn_nonnegative
-- name    : AvramDividend.Classical.causal_l1_primitive_continuousOn_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T23:11:48.99758+00:00
-- url     : https://prove2.me/theorems/c811dc80-c349-4123-b8d5-dcff0936a9b2
-- title:
--   Positive causal primitive of an L1 kernel is continuous through time zero
-- statement:
--   If K is Lebesgue L1 on strictly positive times, the causal primitive x↦∫_(0,x]K(s)ds is continuous on [0,∞), including the origin. Extend K by zero to negative times and apply Mathlib's continuous_primitive theorem for globally integrable functions. This is the endpoint-continuity step for Volterra fixed-point operators.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
open MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.causal_l1_primitive_continuousOn_nonnegative
    (K : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ContinuousOn (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, K s ∂volume)
      (Ici (0 : ℝ)) := by sorry
