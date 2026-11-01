-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_source_fixed_terminal_strict_drawdown_full_measure
-- name    : AvramDividend.Classical.avram_wave4_04_ubv_source_fixed_terminal_strict_drawdown_full_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:24:35.528618+00:00
-- url     : https://prove2.me/theorems/48a9464f-cd44-4e5c-8207-263616d7bedf
-- title:
--   Actual unbounded-variation Lévy process cannot finish a positive deterministic horizon at its running maximum
-- statement:
--   At each strictly positive deterministic horizon T, the original spectrally negative Lévy process X with unbounded variation has a strictly negative terminal drawdown X_T-X_s for some earlier time s≤T almost surely. Combining already Proved original-process small-time negative regularity with original-path fixed-horizon finite-dimensional reversal establishes this without a Brownian or Poisson surrogate and without joint-law replacement. This is a key source-X cap-occupation obstruction: a capped controlled surplus U_t=C would require X_t-X_s≥0 for all earlier surviving s whenever dividends are increasing. The theorem alone does not prove the continuous-time occupation nullity or the full controlled Ito-Meyer estimate.
-- source:
--   Original Lévy source: canonical Proved ae_negative_near_zero_of_unbounded_variation UUID 703dc740-a8df-4cd1-9ff1-622fd81d68c7; canonical Proved avram_ws01e_b_fixed_horizon_strict_reversal UUID a0501c79-2903-44d4-b2cd-38530ae41f34. Principal step: almost-sure initial negative visit makes prefix-minimum strict event full-measure; genuine finite-path reversal transfers full probability to terminal drawdown at T.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fixed_horizon_strict_reversal

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04_ubv_source_fixed_terminal_strict_drawdown_full_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (T : ℝ≥0) (hT : 0 < T) :
    P {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X T ω - X.X s ω < 0} =
      P Set.univ := by sorry
