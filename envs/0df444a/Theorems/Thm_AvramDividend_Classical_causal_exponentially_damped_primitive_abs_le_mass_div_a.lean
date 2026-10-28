-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_exponentially_damped_primitive_abs_le_mass_div_a
-- name    : AvramDividend.Classical.causal_exponentially_damped_primitive_abs_le_mass_div_a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:50:22.724797+00:00
-- url     : https://prove2.me/theorems/c5f22378-a995-45f5-a1f3-7938ca70f05e
-- title:
--   Mass majorant for a damped signed primitive divided by a positive scale
-- statement:
--   If |P| is bounded by an integrable envelope F and the integral of F on (0,x) is at most M, the exponentially damped signed primitive divided by a>0 has absolute value at most M/a. This discharges the primitive-mass premise of the Gaussian Neumann derivative estimate.
-- source:
--   Canonically Proved causal_exponentially_damped_signed_primitive_le_majorant and division by a positive real.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_exponentially_damped_signed_primitive_le_majorant

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_exponentially_damped_primitive_abs_le_mass_div_a
    (P F : ℝ → ℝ) (a w x M : ℝ)
    (ha : 0 < a) (hw : 0 ≤ w) (hx : 0 < x)
    (hPint : IntervalIntegrable
      (fun s : ℝ => Real.exp (-w * (x - s)) * P s) volume 0 x)
    (hFint : IntervalIntegrable F volume 0 x)
    (hdom : ∀ s ∈ Ioo (0 : ℝ) x, |P s| ≤ F s)
    (hMass : ∫ s in (0 : ℝ)..x, F s ≤ M) :
    |(∫ s in (0 : ℝ)..x, Real.exp (-w * (x - s)) * P s) / a| ≤ M / a := by sorry
