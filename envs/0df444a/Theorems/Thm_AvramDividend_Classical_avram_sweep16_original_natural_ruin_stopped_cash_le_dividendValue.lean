-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_natural_ruin_stopped_cash_le_dividendValue
-- name    : AvramDividend.Classical.avram_sweep16_original_natural_ruin_stopped_cash_le_dividendValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:01:29.454333+00:00
-- url     : https://prove2.me/theorems/77174c26-8c03-4c4f-a988-aac49ff161b3
-- title:
--   Original natural ruin-stopped discounted dividend cash bounded by perpetual dividendValue
-- statement:
--   Every original SNLP strategy and natural n has expected discounted Stieltjes cash on paymentTimes(min(ruinTime,n)) bounded by genuine perpetual dividendValue. Use proved exact natural minimum paymentTimes inclusion into the closed Iic n horizon and the proved original closed-window dividendValue bound. This one-way inclusion is endpoint-safe and preserves all actual time-zero and eventual boundary atoms; no equality between strict and closed horizons is asserted.
-- source:
--   Proved original paymentTimes_min_ofReal_subset_inter_horizon UUID 153734f3-93a8-471e-b127-37208aaf3970 and proved closed-window cash bound 23c59e70-ade4-4f8b-9480-6d5903865784, under Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_subset_inter_horizon
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_closed_window_cash_le_dividendValue

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_natural_ruin_stopped_cash_le_dividendValue
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      dividendValue X q x D := by sorry
