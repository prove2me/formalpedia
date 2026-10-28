-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_exp_weighted_scaled_primitive_hasDerivAt_local
-- name    : AvramDividend.Classical.causal_exp_weighted_scaled_primitive_hasDerivAt_local
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:22:41.276173+00:00
-- url     : https://prove2.me/theorems/4e4c7c25-8ede-4ae9-9615-d65cc6f200cd
-- title:
--   Derivative of a scale-normalised exponentially damped causal primitive
-- statement:
--   For a locally integrable exponentially weighted forcing, the damped primitive divided by a fixed Gaussian Volterra coefficient a has derivative g(x)/a minus w times the scaled primitive. Supplies each signed Neumann-series term's precise HasDerivAt premise.
-- source:
--   Canonically Proved causal_exp_weighted_primitive_hasDerivAt_local, HasDerivAt.div_const and ring.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_exp_weighted_primitive_hasDerivAt_local

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_exp_weighted_scaled_primitive_hasDerivAt_local
    (g : ℝ → ℝ) (a w : ℝ)
    (hInt : ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => Real.exp (w * s) * g s) volume 0 x)
    (hCont : ContinuousOn (fun s : ℝ => Real.exp (w * s) * g s)
      (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 < x →
      HasDerivAt (fun y : ℝ =>
        (Real.exp (-w * y) *
          (∫ s in Ioc (0 : ℝ) y,
            Real.exp (w * s) * g s ∂volume)) / a)
        (g x / a - w *
          ((Real.exp (-w * x) *
            (∫ s in Ioc (0 : ℝ) x,
              Real.exp (w * s) * g s ∂volume)) / a)) x := by sorry
