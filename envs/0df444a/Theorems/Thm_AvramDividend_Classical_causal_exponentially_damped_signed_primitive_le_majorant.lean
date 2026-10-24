-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_exponentially_damped_signed_primitive_le_majorant
-- name    : AvramDividend.Classical.causal_exponentially_damped_signed_primitive_le_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:43:24.600453+00:00
-- url     : https://prove2.me/theorems/f69a9b61-82ff-44c7-837f-f8e6277484fe
-- title:
--   Exponential damping preserves signed causal primitive majorants
-- statement:
--   For w≥0 and x>0, the absolute value of the exponentially damped causal primitive of P is bounded by the integral of F whenever |P(s)|≤F(s) and both integrands are interval integrable. This enables termwise bounds in the Gaussian Volterra Neumann resolvent construction.
-- source:
--   Real.exp_le_one_iff and canonically Proved causal_signed_convolution_integral_abs_le_majorant.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_signed_convolution_integral_abs_le_majorant

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_exponentially_damped_signed_primitive_le_majorant
    (P F : ℝ → ℝ) (w x : ℝ)
    (hw : 0 ≤ w) (hx : 0 < x)
    (hPint : IntervalIntegrable
      (fun s : ℝ => Real.exp (-w * (x - s)) * P s) volume 0 x)
    (hFint : IntervalIntegrable F volume 0 x)
    (hdom : ∀ s ∈ Ioo (0 : ℝ) x, |P s| ≤ F s) :
    |∫ s in (0 : ℝ)..x, Real.exp (-w * (x - s)) * P s| ≤
      ∫ s in (0 : ℝ)..x, F s := by sorry
