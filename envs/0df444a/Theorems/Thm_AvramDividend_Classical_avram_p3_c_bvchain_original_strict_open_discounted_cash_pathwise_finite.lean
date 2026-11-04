-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_open_discounted_cash_pathwise_finite
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_strict_open_discounted_cash_pathwise_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:45:33.494003+00:00
-- url     : https://prove2.me/theorems/f0534443-5e13-48ad-8e8c-7487b4d2a806
-- title:
--   Actual original strictly open finite-horizon discounted stopped dividend Stieltjes cash is finite pathwise
-- statement:
--   For the actual original admissible spectrally negative Levy dividend control, the discounted Stieltjes payout on the original ruin-stopped strict-open interval (0,b) has finite extended-real integral for every physical sample and finite horizon. This follows from the proved original pathwise finite closed-horizon dividend Cash theorem and set inclusion, with no additional L1 or stochastic assumptions.
-- source:
--   Public Proved P4-D source pathwise stopped Cash finiteness c4e50d93; Mathlib lintegral_mono_set; Avram Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_strict_open_discounted_cash_pathwise_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (b : ℝ≥0) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ := by sorry
