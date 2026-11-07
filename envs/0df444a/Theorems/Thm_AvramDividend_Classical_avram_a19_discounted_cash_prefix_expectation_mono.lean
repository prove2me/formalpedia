-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_discounted_cash_prefix_expectation_mono
-- name    : AvramDividend.Classical.avram_a19_discounted_cash_prefix_expectation_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:23:02.598698+00:00
-- url     : https://prove2.me/theorems/400f6029-d5d8-4c1e-9d8a-9928f3fa6361
-- title:
--   Original discounted Stieltjes cash prefix expectation monotonicity
-- statement:
--   Integrable original dividend cash at two strict horizons is monotone in expectation when the later horizon is almost surely finite as an ENNReal Stieltjes integral. Includes an arbitrary path-dependent payment-time barrier sigma.
-- source:
--   Follow-on real-expectation bridge in the Avram original BV positive-horizon prebudget a19d8b28, derived from the public pathwise discounted cash-prefix monotonicity helper.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_discounted_cash_prefix_expectation_mono
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞)
    (q s T : ℝ) (hst : s ≤ T)
    (hFinite : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (σ ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≠ ⊤)
    (hIs : Integrable (fun ω =>
      (∫⁻ t in paymentTimes (σ ω) ∩ Iio s,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P)
    (hIT : Integrable (fun ω =>
      (∫⁻ t in paymentTimes (σ ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P) :
    (∫ ω, (∫⁻ t in paymentTimes (σ ω) ∩ Iio s,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) ≤
    (∫ ω, (∫⁻ t in paymentTimes (σ ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) := by sorry
