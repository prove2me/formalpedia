-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_all_random_stop_cash_zero_closed_or_ruin_open
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_all_random_stop_cash_zero_closed_or_ruin_open
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:06:18.496224+00:00
-- url     : https://prove2.me/theorems/4f7a1823-0a00-4d4d-b83e-e53a553d65cc
-- title:
--   Complete original stopped dividend Cash endpoint selector: exact time-zero right atom, surviving closed horizon, positive-ruin open horizon
-- statement:
--   For the actual original P4-F random stopped clock τ≤ruinTime and full paid Stieltjes Cash, exactly one of three paths occurs: τ=0 pays the full initial right-atom; 0<τ<ruin pays the closed horizon including the right atom at τ; τ=positive ruin pays only up to the open horizon excluding the ruin-time right atom. The theorem combines independently checked original-source zero-clock and positive-clock endpoint lemmas, preserving singular-continuous mass, simultaneous source/right-payment order and the original paymentTimes definition.
-- source:
--   Original P4-D zero clock Cash source helper UUID 5514c6b0-2fb0-4573-ac0b-260d31a846f8 (proof pending at authoring) and positive random endpoint helper UUID 2f691f7a-6ffb-4501-a070-77762f495f64 (Proved).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_positive_random_stop_closed_or_ruin_open_cash
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_all_random_stop_cash_zero_closed_or_ruin_open
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hτle : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (ω : Ω) :
    Cash ω =
      if τ ω = 0 then
        (ENNReal.ofReal (rightLimit D 0 ω - D 0 ω)).toReal
      else if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        (∫⁻ s in Icc (0 : ℝ) (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal
      else
        (∫⁻ s in Ico (0 : ℝ) (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal := by sorry
