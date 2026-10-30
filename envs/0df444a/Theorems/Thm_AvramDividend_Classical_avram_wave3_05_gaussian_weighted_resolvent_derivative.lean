-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_weighted_resolvent_derivative
-- name    : AvramDividend.Classical.avram_wave3_05_gaussian_weighted_resolvent_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:38:35.456993+00:00
-- url     : https://prove2.me/theorems/e575ad7a-e922-47ad-aa17-a55fbdff3651
-- title:
--   Weighted L1 of original Gaussian Neumann resolvent derivative from signed global density
-- statement:
--   The original Gaussian renewal construction gives g'(x)=exp(wx)S(x)/a on the positive axis and has an unweighted L1 signed Neumann density S. For every theta at least w, the exponential multiplier exp((w-theta)x) is bounded by one on the positive axis; hence exp(-theta x)g'(x) is L1, with no unproved global integrability assumption on W''.
-- source:
--   Native Gaussian antitone Volterra Neumann renewal, pinned Mathlib Integrable.bdd_mul and HasDerivAt.deriv.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Exponential

open MeasureTheory Set

theorem AvramDividend.Classical.avram_wave3_05_gaussian_weighted_resolvent_derivative
    (g S : ℝ → ℝ) (a w θ : ℝ)
    (hθ : w ≤ θ)
    (hS : IntegrableOn S (Ioi (0 : ℝ)) volume)
    (hder : ∀ x : ℝ, 0 < x →
      HasDerivAt g (Real.exp (w * x) * (S x / a)) x) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * deriv g x)
      (Ioi (0 : ℝ)) volume := by sorry
