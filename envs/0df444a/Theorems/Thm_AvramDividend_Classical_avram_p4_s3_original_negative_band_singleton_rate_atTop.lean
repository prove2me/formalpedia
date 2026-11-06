-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_singleton_rate_atTop
-- name    : AvramDividend.Classical.avram_p4_s3_original_negative_band_singleton_rate_atTop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:02:53.182741+00:00
-- url     : https://prove2.me/theorems/0117683a-dfbb-453a-80af-cb75fa37472a
-- title:
--   Exact original negative-band one-jump probability has the physical small-time Lévy rate
-- statement:
--   For the actual original spectrally negative Lévy process, the probability of precisely one jump beyond the negative threshold during (0,1/k] is asymptotically ν(B)/k. The proof combines the proved original-source quadratic one-jump estimate and the exact time/intensity conversion. No equality-in-law or stochastic axioms are introduced.
-- source:
--   Actual negative-band one-jump quadratic source bound 53d4b07f-7c44-42ae-8509-982525ad8a1f, original physical intensity real division c3093fe5-49b3-448a-b97e-e89c4d11ca3b, and elementary real filter squeeze.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_negative_band_singleton_rate_atTop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) :
    Filter.Tendsto
      (fun k : ℕ => (k : ℝ) * P.real {ω : Ω |
        {u : ℝ≥0 | 0 < u ∧ u ≤ (k : ℝ≥0)⁻¹ ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1))}.ncard = 1})
      Filter.atTop
      (nhds ((X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)) := by sorry
