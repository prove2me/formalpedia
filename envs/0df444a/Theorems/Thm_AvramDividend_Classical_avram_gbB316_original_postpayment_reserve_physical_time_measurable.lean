-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB316_original_postpayment_reserve_physical_time_measurable
-- name    : AvramDividend.Classical.avram_gbB316_original_postpayment_reserve_physical_time_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:07:08.243608+00:00
-- url     : https://prove2.me/theorems/024e2b16-94c7-41a0-99d0-697d1ddedc73
-- title:
--   Every original adapted dividend postpayment reserve sample has measurable real physical-time section
-- statement:
--   For any adapted original dividend strategy of a spectrally negative Lévy source and every sample, the physical real-time section of the postpayment reserve, with native Real.toNNReal source time, is measurable. Follows from the Proved B269 joint source time-sample measurability by composing with the measurable physical-time pair map. Needed to apply continuity from above of shrinking level bands in Gaussian B141.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB316_original_postpayment_reserve_physical_time_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (ω : Ω) :
    Measurable (fun t : ℝ =>
      x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω) := by sorry
