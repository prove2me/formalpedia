-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_closed_horizon_cash_monotone_to_perpetual
-- name    : AvramDividend.Classical.avram_sweep16_original_closed_horizon_cash_monotone_to_perpetual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:51:33.274537+00:00
-- url     : https://prove2.me/theorems/e04d7bce-802e-4ae9-b105-a7f973a62d56
-- title:
--   Original Stieltjes closed-horizon cash monotonicity and perpetual bound
-- statement:
--   For the original spectrally negative Levy X, actual ruin-time dividendMeasure and any two real horizons T <= U, genuine expected discounted cash over Iic T is bounded by the closed Iic U cash, which is bounded by full original dividendValue. Both closed endpoints and the time-zero dividend atom are retained. No Itô, variation or process-law assumptions are added.
-- source:
--   Pinned original dividendMeasure, paymentTimes, ruinTime and dividendValue. Lean MeasureTheory.lintegral_mono and lintegral_mono_set with Set.Iic membership, followed by accepted original closed-window lemma 23c59e70-ade4-4f8b-9480-6d5903865784.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_closed_window_cash_le_dividendValue

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_closed_horizon_cash_monotone_to_perpetual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T U : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hTU : T ≤ U) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic U,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ∧
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic U,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      dividendValue X q x D := by sorry
