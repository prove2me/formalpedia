-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_positive_random_stop_closed_or_ruin_open_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_positive_random_stop_closed_or_ruin_open_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:46:06.648128+00:00
-- url     : https://prove2.me/theorems/2f691f7a-6ffb-4501-a070-77762f495f64
-- title:
--   Original positive stopped dividend cash includes a surviving horizon right atom and excludes the positive-ruin endpoint
-- statement:
--   At a positive original stopping horizon τ dominated by ruinTime, the exact full paid Stieltjes Cash equals a closed Icc[0,τ] integral if τ<ruin and an open Ico[0,τ) integral if τ=ruin. This matches simultaneous source/right-payment ordering, keeps the initial right atom, includes a surviving horizon right-payment atom and excludes the positive-ruin endpoint. No derivative boundary assumption is used.
-- source:
--   Proved original strict horizon paymentTimes equality a042792f-d262-4aca-99d5-96410159fb13 and proved P4-D positive ruin cash exclusion 2ea65148-498f-4c44-ba23-93837b941444.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_paymentTimes_strict_horizon_eq_Icc
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_positive_ruin_cash_excludes_terminal_atom
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_positive_random_stop_closed_or_ruin_open_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hτle : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (ω : Ω) (hPos : 0 < τ ω) :
    Cash ω =
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        (∫⁻ s in Icc (0 : ℝ) (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal
      else
        (∫⁻ s in Ico (0 : ℝ) (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal := by sorry
