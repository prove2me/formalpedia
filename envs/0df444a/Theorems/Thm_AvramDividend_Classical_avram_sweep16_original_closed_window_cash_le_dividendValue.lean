-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_closed_window_cash_le_dividendValue
-- name    : AvramDividend.Classical.avram_sweep16_original_closed_window_cash_le_dividendValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:21:26.748196+00:00
-- url     : https://prove2.me/theorems/23c59e70-ade4-4f8b-9480-6d5903865784
-- title:
--   Original finite closed-horizon Stieltjes dividend cash is bounded by perpetual dividendValue
-- statement:
--   For every original spectrally negative Levy process, arbitrary dividend path and any real horizon, the double ENNReal discounted Stieltjes payout on genuine paymentTimes(ruinTime) intersect Iic T is bounded by the corresponding full original dividendValue. This is pointwise measure restriction monotonicity, including time zero and the closed horizon endpoint; no bounded-variation or Itô assumptions are used.
-- source:
--   Original dividendValue and paymentTimes definitions; Lean MeasureTheory.lintegral_mono_set and lintegral_mono, with the set inclusion (paymentTimes ruin ∩ Iic T) ⊆ paymentTimes ruin.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_closed_window_cash_le_dividendValue
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      dividendValue X q x D := by sorry
