-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_ordered_clocks_closed_cash_L1
-- name    : AvramDividend.Classical.avram_ubv_loc6_original_ordered_clocks_closed_cash_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:55:33.34485+00:00
-- url     : https://prove2.me/theorems/6a275c18-5e27-4e8b-8eec-7c8a28e0033f
-- title:
--   Original closed-Iic discounted Stieltjes cash is L1 under any earlier measurable spatial localisation
-- statement:
--   For the actual original spectrally negative Levy dividend model, any measurable clock σ≤τ has an integrable original closed-payment Stieltjes cash if the same exact cash at τ is integrable. Includes all time-zero and horizon right-payment atoms, and relies on source finiteness of the literal discounted Stieltjes measure, genuine random-upper-clock cash measurability and monotonicity. It does not postulate martingale integrability or a candidate value growth bound.
-- source:
--   UBV-LOC6 original physical clipped cash L1 source bridge for fa7052b1 and f12, importing previously Proved original random cash measurability 2d478c7d and exact stopped cash finiteness c4e50d93.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_loc6_original_ordered_clocks_closed_cash_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ τ : Ω → ℝ≥0) (hστ : ∀ ω, σ ω ≤ τ ω)
    (hσmeas : Measurable (fun ω => (σ ω : ℝ)))
    (hCashτI : Integrable (fun ω => (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P) :
    Integrable (fun ω => (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P := by sorry
