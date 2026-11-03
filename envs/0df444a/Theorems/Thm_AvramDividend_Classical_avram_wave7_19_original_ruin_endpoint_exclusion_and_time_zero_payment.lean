-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ruin_endpoint_exclusion_and_time_zero_payment
-- name    : AvramDividend.Classical.avram_wave7_19_original_ruin_endpoint_exclusion_and_time_zero_payment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:53:26.883219+00:00
-- url     : https://prove2.me/theorems/d68c1081-c210-486c-9517-59b67cb19632
-- title:
--   Original dividend measure payment support includes time zero even on immediate ruin but excludes all strictly positive ruin endpoints
-- statement:
--   The exact original paymentTimes support includes time zero even when ruinTime is 0, so any predictable initial right dividend must be accounted. At strictly positive original ruin times, including jump overshoot or downward creeping cases, equality of the physical time with ruinTime excludes a dividend payment at the endpoint. This is a direct definition-based boundary identity, independent of any false path-continuity claim.
-- source:
--   Original Definitions.Def_AvramDividend_Classical_DividendStrategy paymentTimes and ruinTime; no extra path assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_ruin_endpoint_exclusion_and_time_zero_payment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (0 : ℝ) ∈ paymentTimes (ruinTime X x D ω) ∧
    (∀ t : ℝ, 0 < t → ENNReal.ofReal t = ruinTime X x D ω →
      t ∉ paymentTimes (ruinTime X x D ω)) := by sorry
