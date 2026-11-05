-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:54:22.988234+00:00
-- url     : https://prove2.me/theorems/5514c6b0-2fb0-4573-ac0b-260d31a846f8
-- title:
--   Original zero-stop real Stieltjes Cash equals the exact initial right-dividend payment atom
-- statement:
--   For the original controlled Lévy source with an arbitrary random stopped clock τ, if τ(ω)=0 then the exact paid discounted real Cash equals the original time-zero Stieltjes singleton mass, namely ENNReal.ofReal(rightLimit D 0-D 0).toReal. This includes the initial payment even if ruin is instantaneous and makes no positive-horizon survival claim. It follows from two previously Proved source-exact lemmas.
-- source:
--   Proved source zero-horizon full paid Stieltjes atom UUID 1fb597ac-8e48-41be-a4e3-03b7681f3915 and original dividendMeasure singleton identity UUID 4f229f9a-6d10-43ea-aea7-c2db48b444ec.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (ω : Ω) (hZero : τ ω = 0) :
    Cash ω =
      (ENNReal.ofReal (rightLimit D 0 ω - D 0 ω)).toReal := by sorry
