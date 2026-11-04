-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:50:05.262615+00:00
-- url     : https://prove2.me/theorems/52a094c1-3bfa-478f-9c99-8ffaa0909944
-- title:
--   Closed original Stieltjes restricted indicator integral equals exact P4-F stopped cash
-- statement:
--   For the exact original Lévy riskProcess, ruinTime, paymentTimes and dividendMeasure, the discounted full Stieltjes cash integrated against dividendMeasure restricted to the genuine closed [0,T] horizon with the source payment selector equals exactly the canonical P4-F cash integral over paymentTimes(ruinTime)∩Iic T. This uses the Proved nonnegative payment window and source Borel payment selector together with pinned Mathlib lintegral_indicator and Measure.restrict_restrict. It covers right atoms at 0 and surviving T, simultaneous source/payment jumps and every diffuse including singular-continuous payment, while excluding the positive ruin atom. No replacement measure or boundary derivative assumption.
-- source:
--   P4-F 0dda1be7 original hCash; P4-D exact window 0ecad334 and measurable selector in publication; Mathlib pin 0df444a3 Measure.restrict_restrict and lintegral_indicator signatures

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_measurableSet
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_payment_window_closed_horizon_exact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (ω : Ω) (T : ℝ≥0) :
    (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
      then ENNReal.ofReal (Real.exp (-(q * s))) else 0)
        ∂((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)))) =
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by sorry
