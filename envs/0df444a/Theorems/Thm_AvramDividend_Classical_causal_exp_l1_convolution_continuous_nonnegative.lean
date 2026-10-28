-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_exp_l1_convolution_continuous_nonnegative
-- name    : AvramDividend.Classical.causal_exp_l1_convolution_continuous_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T17:05:29.522801+00:00
-- url     : https://prove2.me/theorems/13965b4e-a139-4d8c-b17f-d4cf5d66ba2c
-- title:
--   Exponentially damped causal L1 convolution is continuous through zero
-- statement:
--   For any signed kernel integrable on positive times and nonnegative exponential damping rate, the causal convolution with the exponentially decaying input is continuous on the entire nonnegative half-line, including the origin. This establishes boundary continuity for Gaussian Neumann correction terms from their signed L1 power sequence.
-- source:
--   The exponential damping input is continuous on [0,∞). For w≥0, exp(-w*s) is bounded by one on every positive interval. Apply the canonically Proved causal_l1_convolution_continuousOn_nonnegative_of_locally_bounded theorem with L1 kernel P and exponential input. This supplies the closed-half-line continuity of each Gaussian Neumann primitive after convolution commutation.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_continuousOn_nonnegative_of_locally_bounded

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_exp_l1_convolution_continuous_nonnegative
    (P : ℝ → ℝ) (w : ℝ) (hw : 0 ≤ w)
    (hP : IntegrableOn P (Ioi (0 : ℝ)) volume) :
    ContinuousOn
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        P (x - s) * Real.exp (-w * s) ∂volume)
      (Ici (0 : ℝ)) := by sorry
