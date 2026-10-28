-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_positive_envelope_mass_lt_a
-- name    : AvramDividend.Classical.causal_weighted_positive_envelope_mass_lt_a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:05:39.279993+00:00
-- url     : https://prove2.me/theorems/64b9a419-7191-4e00-a367-345c97ba4f84
-- title:
--   Strict weighted mass bound for the positive Gaussian Volterra envelope
-- statement:
--   For positive exponential damping w and an integrable damped real kernel, the integrable envelope e^(-wt)(|β|+K(t)) has total positive-time mass strictly less than the coefficient a whenever |β|/w plus the weighted absolute mass of K is less than a. This supports the contraction ratio needed to build nonnegative dominating convolution powers.
-- source:
--   Pinned positive_laplace_constant_reference and measure-theoretic additivity/monotonicity; adapt the accepted positive_weighted_full_kernel_norm_small proof.

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_positive_laplace_constant_reference

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_weighted_positive_envelope_mass_lt_a
    (K : ℝ → ℝ) (a β w : ℝ) (hw : 0 < w)
    (hKi : IntegrableOn (fun t : ℝ => Real.exp (-w * t) * K t)
      (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a) :
    IntegrableOn (fun t : ℝ =>
      Real.exp (-w * t) * (|β| + K t))
      (Ioi (0 : ℝ)) volume ∧
    (∫ t in Ioi (0 : ℝ),
      Real.exp (-w * t) * (|β| + K t) ∂volume) < a := by sorry
