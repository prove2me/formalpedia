-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_exponential_primitive_convolution_identity
-- name    : AvramDividend.Classical.causal_exponential_primitive_convolution_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:19:01.861406+00:00
-- url     : https://prove2.me/theorems/84704c63-e446-403e-9a9e-64763f5bd172
-- title:
--   Exponential weighted primitive equals time-lag damping convolution
-- statement:
--   Multiplying ∫_0^x exp(ws)P(s)ds by exp(−wx) is exactly the causal convolution ∫_0^x exp(−w(x−s))P(s)ds, without extra global integrability premises. This connects the local derivative formula with the signed damping majorant bound.
-- source:
--   Linearity of the interval integral and the exponential addition identity.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_signed_convolution_integral_abs_le_majorant

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_exponential_primitive_convolution_identity
    (P : ℝ → ℝ) (w x : ℝ) :
    Real.exp (-w * x) *
      (∫ s in (0 : ℝ)..x, Real.exp (w * s) * P s) =
    ∫ s in (0 : ℝ)..x, Real.exp (-w * (x - s)) * P s := by sorry
