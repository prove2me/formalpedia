-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_measurable_stop_real_budget_to_ennreal
-- name    : AvramDividend.Classical.avram_wave5_05_original_measurable_stop_real_budget_to_ennreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:38:06.699014+00:00
-- url     : https://prove2.me/theorems/92ec1f68-7536-4cab-bc15-8d304dcbbbb6
-- title:
--   Original complete stopped real Stieltjes reward budget implies ENNReal budget
-- statement:
--   For a genuine spectrally negative Lévy source X and true admissible regulator D, any measurable stopping clock S and finite complete ruin-stopped expected cash envelope, a real expected stopped discounted complete Stieltjes reward bound by B implies the exact ENNReal stopped reward bound by ofReal B. Includes payment at time zero, singular-continuous dividends and pre-ruin right-jump atoms. No martingale identity or extra drift hypothesis is asserted; this transfers only real to ENNReal, using accepted original stopped cash measurability and integrability.
-- source:
--   Avram-Palmowski-Pistorius (2007), stopped verification real-valued localization; accepted source helpers 014f398c-65e1-4223-b742-2101fd8ad500 and 8515deec-a00c-4316-8dfa-44a8f79ae6dd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_measurable_stopping_clock_complete_stieltjes_real_ennreal_expectation_eq
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_05_original_measurable_stop_real_budget_to_ennreal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (q : ℝ)
    (S : Ω → ℝ≥0∞) (hSm : Measurable S)
    (hCashFinite :
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂dividendMeasure D ω ∂P) < ⊤)
    (B : ℝ)
    (hRealBudget :
      (∫ ω,
        (∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (S ω)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂dividendMeasure D ω).toReal ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (S ω)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂dividendMeasure D ω ∂P) ≤ ENNReal.ofReal B := by
  sorry
