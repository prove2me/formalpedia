-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB109_original_postpayment_countable_discontinuity_time_measure_null
-- name    : AvramDividend.Classical.avram_gbB109_original_postpayment_countable_discontinuity_time_measure_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:50:28.143346+00:00
-- url     : https://prove2.me/theorems/c67326ca-8a5f-4661-abb7-45c075fef5e1
-- title:
--   Original zero-jump reserve discontinuity time set is null for any null-singleton time measure
-- statement:
--   The already Proved B80 theorem gives countability of the physical postpayment reserve discontinuity times almost surely. In the exact pinned Mathlib environment, Set.Countable.measure_zero requires NullSingletonClass μ. Thus under any such NNReal time measure μ the original reserve discontinuity set has μ-measure zero. This supplies an actual B102 exceptional-set prerequisite without an unsupported NNReal volume instance.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB80_original_zerojump_postpayment_ae_countable_discontinuities
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB109_original_postpayment_countable_discontinuity_time_measure_null
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (μ : Measure ℝ≥0) [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, μ
      {t : ℝ≥0 | ¬ ContinuousAt
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t} = 0 := by sorry
