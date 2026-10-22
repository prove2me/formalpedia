-- Prove2me | Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_continuous_excursion_log_derivative
-- name    : AvramDividend.Classical.contDiffOn_one_of_continuous_excursion_log_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T22:42:08.134527+00:00
-- url     : https://prove2.me/theorems/7985d7ce-6f65-4778-a254-f0fede56db4b
-- title:
--   Continuous excursion log-derivative formula implies C1 regularity
-- statement:
--   Suppose a real-valued function W is differentiable at every strictly positive point and its derivative factorises as W'(x) = W(x) (phi + T(x)), where T is continuous on the positive half-line. Then W is continuously differentiable there. This is the deterministic calculus bridge from a continuous excursion-height tail to scale-function C1 regularity, without any stochastic assumptions.
-- source:
--   Mathlib.Analysis.Calculus.ContDiff.Deriv: contDiffOn_one_iff_derivWithin; deterministic consequence of the excursion-tail derivative representation in Kyprianou, Kuznetsov and Rivero (2012), The Theory of Scale Functions for Spectrally Negative Levy Processes.

import Mathlib
open Set

theorem AvramDividend.Classical.contDiffOn_one_of_continuous_excursion_log_derivative
    (W T : ℝ → ℝ) (φ : ℝ)
    (hd : ∀ x : ℝ, x ∈ Ioi (0 : ℝ) → DifferentiableAt ℝ W x)
    (hT : ContinuousOn T (Ioi (0 : ℝ)))
    (hDeriv : ∀ x : ℝ, x ∈ Ioi (0 : ℝ) →
      deriv W x = W x * (φ + T x)) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by sorry
