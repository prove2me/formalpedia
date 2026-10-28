-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_continuous_halfline_window_integrable_extension
-- name    : AvramDividend.Classical.causal_continuous_halfline_window_integrable_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:00:15.643458+00:00
-- url     : https://prove2.me/theorems/a734a09b-06fe-45b4-8c7e-538f6ddbfcec
-- title:
--   Continuous integrable cut-off preserving a positive-time window
-- statement:
--   For a function continuous on nonnegative times and any R>0, construct a continuous-on-nonnegative-time function which is integrable over positive times and agrees with the original function on [0,R]. The construction clamps the input to R and multiplies by a continuous unit plateau which tapers to zero between R and R+1. This is a localisation step required for the causal convolution C1 smoothing theorem.
-- source:
--   Classical continuous compact-support taper and Mathlib ContinuousOn.integrableOn_Icc, IntegrableOn.of_forall_sdiff_eq_zero.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
open MeasureTheory Set

theorem AvramDividend.Classical.causal_continuous_halfline_window_integrable_extension
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (R : ℝ) (hR : 0 < R) :
    ∃ F : ℝ → ℝ,
      ContinuousOn F (Ici (0 : ℝ)) ∧
      IntegrableOn F (Ioi (0 : ℝ)) volume ∧
      (∀ t ∈ Icc (0 : ℝ) R, F t = f t) := by sorry
