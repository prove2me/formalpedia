-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
-- name    : AvramDividend.Classical.avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:20:04.815217+00:00
-- url     : https://prove2.me/theorems/014f398c-65e1-4223-b742-2101fd8ad500
-- title:
--   Full original controlled Stieltjes reward remains measurable at any measurable random stop
-- statement:
--   For a native spectrally negative Levy source X and its unchanged adapted dividend strategy D, the complete discounted full Stieltjes dividend reward, restricted to times before both the original controlled ruin and an arbitrary ambient-measurable sample-path clock S, is an ENNReal-valued measurable random variable. The proof uses native ruin stopping/measurability, the original s-finite dividend-measure kernel, the joint payment-times measurable set and measurable random indicator integral. No finite-variation surrogate or added HJB assumption. Includes time-zero right dividend atom and all diffuse/singular/right-atomic payments.
-- source:
--   Source-faithful Lévy stopped dividend kernel, Avram et al. (2007) Proposition 4(i).

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

theorem AvramDividend.Classical.avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (S : Ω → ℝ≥0∞) (hSm : Measurable S) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (S ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) := by
  sorry
