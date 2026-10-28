-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_Ioc_integral_interior_congr
-- name    : AvramDividend.Classical.causal_Ioc_integral_interior_congr
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:49:29.491694+00:00
-- url     : https://prove2.me/theorems/32cb96df-bca5-478e-b5e8-5bbe09b27a2a
-- title:
--   Causal Lebesgue integrals agree under equality on the open interior
-- statement:
--   Real Lebesgue integrals over (0,x] are identical for two functions that agree at every strictly interior time 0<s<x. This handles the measure-zero endpoint when converting the Gaussian Neumann kernel to the undamped Volterra kernel.
-- source:
--   Apply the pinned Mathlib endpoint-nullset identity integral_Ioc_eq_integral_Ioo for Lebesgue measure. On the common open interior, apply almost-everywhere integral congruence. Needed to untwist the damped signed kernel inside a causal convolution despite its different value at the zero endpoint.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set

theorem AvramDividend.Classical.causal_Ioc_integral_interior_congr
    (f g : ℝ → ℝ) (x : ℝ)
    (hfg : ∀ s : ℝ, 0 < s → s < x → f s = g s) :
    (∫ s in Ioc (0 : ℝ) x, f s ∂volume) =
      (∫ s in Ioc (0 : ℝ) x, g s ∂volume) := by sorry
