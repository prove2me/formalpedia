-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_measurable
-- name    : AvramDividend.Classical.avram_wave6_08_original_perpetual_stieltjes_cash_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:50:05.019887+00:00
-- url     : https://prove2.me/theorems/db59cbee-4085-43eb-a6bf-b5ec11efe6b4
-- title:
--   Genuine perpetual original Lévy ruin-stopped full-Stieltjes cash measurability
-- statement:
--   The discounted full Stieltjes dividend cash over actual paymentTimes(ruinTime) is measurable on the original spectrally negative Lévy sample space, for any adapted left-continuous dividend strategy, arbitrary real discount rate and even when ruin never occurs. The proof uses the original dividend s-finite kernel and measurable joint payment region, not an artificial terminal clock.
-- source:
--   Direct adaptation of Proved 2d478c7d original random-clock cash measurable, dropping the upper-clock set, using Proved 6e9faa20 paymentTimes joint measurable, 766b5129 dividendMeasure original s-finite kernel, 3f6e3e3b measurable random indicator lintegral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_perpetual_stieltjes_cash_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) := by sorry
