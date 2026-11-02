-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
-- name    : AvramDividend.Classical.avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:51:04.328199+00:00
-- url     : https://prove2.me/theorems/2d478c7d-9d35-4371-a220-d9fd063c4852
-- title:
--   Original ruin-stopped complete Stieltjes dividends are measurable with a sample-dependent inclusive upper clock
-- statement:
--   For the genuine spectrally negative Levy X, original left-continuous dividend strategy D and its original ruin time, the complete discounted Stieltjes cash with paymentTimes(ruinTime) intersect Iic(T omega) is a measurable ENNReal random variable for an arbitrary measurable real sample-dependent upper clock T. The right-dividend atom at T<ruin is included, unlike paymentTimes(min(ruin,T)); singular continuous and simultaneous payments are retained. Prove directly from the source sample-dependent payment region measurable theorem and the genuine s-finite dividendMeasure kernel, with no new stochastic assumption.
-- source:
--   Avram Proposition 4(i), exact inclusive stopped cash region. Direct adaptation of Proved 014f398c to a random Iic endpoint, using Proved 6e9faa20,766b5129,3f6e3e3b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (T : Ω → ℝ) (hTm : Measurable T) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) := by sorry
