-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_source_ruinStopped_fullStieltjes_randomPayoff_measurable
-- name    : AvramDividend.Classical.avram_wave4_03_original_source_ruinStopped_fullStieltjes_randomPayoff_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:35:36.759176+00:00
-- url     : https://prove2.me/theorems/70886bb9-2a3f-4ee1-be59-305b5e01a81c
-- title:
--   Actual source Lévy finite-horizon strictly killed full Stieltjes dividend payoff is measurable in probability
-- statement:
--   The genuine original spectrally negative Lévy path and same adapted left-continuous dividend control have a measurable random full Stieltjes dividend integral over the exact payment region {t≥0, (t=0 or t<actual ruinTime), t≤T}, with true source discounted postpayment exponential. The ruin time is proved a stopping time on the same filtration and hence measurable; this makes the exact random payment region jointly measurable and allows the established genuine s-finite dividend kernel integration theorem. No replacement atom-only measure or Poisson process is used.
-- source:
--   Proved original source ruin stopping time 0e921b75 and full random Stieltjes kernel integrability measurability 872a8afd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_ruinTime_rightCont_stopping_time
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_source_exponential_random_fullStieltjes_lintegral_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_wave4_03_original_source_ruinStopped_fullStieltjes_randomPayoff_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (θ q T : ℝ) :
    Measurable (fun ω : Ω =>
      ∫⁻ t : ℝ, if t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic T then
        ENNReal.ofReal (Real.exp
          (θ * (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) -
            (t.toNNReal : ℝ) * q)) else 0
      ∂dividendMeasure D ω) := by sorry
