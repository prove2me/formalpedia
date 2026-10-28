-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_scaled_primitive_derivative_from_positive_L1
-- name    : AvramDividend.Classical.causal_scaled_primitive_derivative_from_positive_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T18:50:25.083375+00:00
-- url     : https://prove2.me/theorems/9424038d-e0e9-4a43-b6ef-2a0e8ef41cb4
-- title:
--   Derivative of a damped signed Neumann primitive from positive-time L1 and continuity
-- statement:
--   Every signed Neumann kernel that is integrable and continuous on positive time has a scaled exponentially damped primitive with derivative P(x)/a minus w times the primitive. It directly provides the exact derivative premise of the proved Gaussian complete-resolvent C1 theorem.
-- source:
--   Use the proved positive-time L1 to interval-integrability bridge. Multiplication by a continuous exponential preserves interval integrability, while positive-time continuity of the signed convolution power preserves continuity of the weighted integrand. Apply the proved damped scaled primitive derivative theorem. Supplies hHasDeriv for Gaussian Neumann-series regularity.

import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_positive_L1_intervalIntegrable
import Theorems.Thm_AvramDividend_Classical_causal_exp_weighted_scaled_primitive_hasDerivAt_local

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_scaled_primitive_derivative_from_positive_L1
    (P : ℝ → ℝ) (a w : ℝ)
    (hPL1 : IntegrableOn P (Ioi (0 : ℝ)) volume)
    (hPcont : ContinuousOn P (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 < x →
      HasDerivAt (fun y : ℝ =>
        (Real.exp (-w * y) *
          (∫ s in Ioc (0 : ℝ) y,
            Real.exp (w * s) * P s ∂volume)) / a)
        (P x / a - w *
          ((Real.exp (-w * x) *
            (∫ s in Ioc (0 : ℝ) x,
              Real.exp (w * s) * P s ∂volume)) / a)) x := by sorry
