-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_volterra_C2_of_C1_derivative_resolvent
-- name    : AvramDividend.Classical.causal_volterra_C2_of_C1_derivative_resolvent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:41:07.658992+00:00
-- url     : https://prove2.me/theorems/f3b0e814-471b-4352-b6ec-1bab501495cd
-- title:
--   Promote an integrated Volterra solution to C2 using a C1 derivative resolvent
-- statement:
--   Assume V is continuous and locally bounded on positive times, satisfies the integrated causal Volterra equation aV+(β+K)*V=x with a>0 and K integrable, and a continuous nonnegative-time derivative resolvent g is C1 on positive times and solves ag+(β+K)*g=1. Then the primitive of g satisfies the same integrated equation and agrees with V by uniqueness. Fundamental theorem of calculus identifies its derivative as g, so V is C2 on positive times.
-- source:
--   Causal Volterra uniqueness, Fubini and fundamental theorem of calculus; an exact intermediary for Chan–Kyprianou–Savov (2011), smoothness of Gaussian scale functions.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set

namespace AvramDividend.Classical

theorem causal_volterra_C2_of_C1_derivative_resolvent
    (K g V : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C)
    (hVe : ∀ x : ℝ, 0 < x →
      a * V x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) = x)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hgC1 : ContDiffOn ℝ 1 g (Ioi (0 : ℝ)))
    (hgeq : ∀ x : ℝ, 0 < x →
      a * g x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * g s ∂volume) = 1) :
    ContDiffOn ℝ 2 V (Ioi (0 : ℝ)) := by sorry

end AvramDividend.Classical
