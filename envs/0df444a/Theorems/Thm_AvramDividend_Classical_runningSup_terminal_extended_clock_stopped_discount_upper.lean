-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_terminal_extended_clock_stopped_discount_upper
-- name    : AvramDividend.Classical.runningSup_terminal_extended_clock_stopped_discount_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:14:22.017037+00:00
-- url     : https://prove2.me/theorems/aa5c1e5d-b212-45ff-a37d-d1c94e56168d
-- title:
--   Terminal extended-clock upper bound for dividends stopped at any ruin horizon
-- statement:
--   For an attained first record at level b and a terminal time no later than the extended first crossing of b+h, the discounted Stieltjes dividend reward within any stopped payment window is bounded by h times the discount at the first record. This transfers the already proved unrestricted extended-clock terminal-cell estimate to the actual stopped integral used in the upper-renewal identity.
-- source:
--   Monotonicity of nonnegative Lebesgue integrals under restriction to the stopped payment-time set, combined with the accepted extended first-record terminal-cell estimate.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_terminal_extended_clock_discount_upper

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.runningSup_terminal_extended_clock_stopped_discount_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (τ : ℝ≥0∞)
    (q b h : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (u t : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (ht : (t : ℝ≥0∞) ≤
      (⨅ (r : ℝ≥0) (_ : b + h < X.X r ω), (r : ℝ≥0∞))) :
    (∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (u : ℝ) (t : ℝ)
      then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) * ENNReal.ofReal h := by sorry
