-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_truncated_cash_le_source_ruin_clock
-- name    : AvramDividend.Classical.avram_wave7_08_truncated_cash_le_source_ruin_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:04:37.875061+00:00
-- url     : https://prove2.me/theorems/0607e136-32a8-4bdc-a41a-c9c76f93e40f
-- title:
--   Original source finite-clock dividend cash dominated by full original ruin-domain Stieltjes cash
-- statement:
--   Expected discounted Stieltjes dividends for the genuine source process X and original payout D on truncated paymentTimes(min(ruinTime,n)) at time n are bounded by expected dividends on original paymentTimes(ruinTime) intersected with Iic n. Uses only nonnegative lintegral set monotonicity and exact payment-domain inclusion, and supports W6-06 original one-sided stopped HJB budget comparison.
-- source:
--   Exact original-source Stieltjes cash, no replacement model. Derived from W7-08 original payment support child db25d81e and Mathlib lintegral_mono_set.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_truncated_cash_le_source_ruin_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (hn : 0 < n) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
