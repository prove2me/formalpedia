-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_strict_future_random_clock_cash_measurable
-- name    : AvramDividend.Classical.avram_wave7_03_original_strict_future_random_clock_cash_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:47:44.358632+00:00
-- url     : https://prove2.me/theorems/ea1c2561-3508-43a7-8d26-861057008c4e
-- title:
--   Original source strict future Stieltjes payout is measurable under any measurable random lower clock
-- statement:
--   For the original spectrally negative Lévy process X under P and the actual ruinTime, paymentTimes, dividendMeasure kernel and right-limit dividend atoms, the unrestricted discounted ENNReal Stieltjes payment in strictly future times t > T ω is a measurable random variable for any measurable real-valued random lower clock T. Strict future Ioi excludes the atom at T and accounts for continuous and jump payments. The kernel calculation is original-source and has no extra finite-variation or stochastic-martingale assumptions.
-- source:
--   Direct adaptation of accepted original inclusive random upper-clock kernel measurability theorem 2d478c7d, changing only the endpoint condition to a strict lower bound, with original paymentTimes joint measurability and dividendMeasure global s-finite kernel.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_03_original_strict_future_random_clock_cash_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (T : Ω → ℝ) (hTm : Measurable T) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) := by sorry
