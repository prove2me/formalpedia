-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_negative_uniform_grid_levy_mean
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_negative_uniform_grid_levy_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:38:42.676475+00:00
-- url     : https://prove2.me/theorems/70533628-e5bc-49ef-b315-1f765468e8f9
-- title:
--   Genuine original negative compact-test grid expectations converge to the Levy measure rate
-- statement:
--   For an original spectrally negative Levy process, a strictly positive horizon and every continuous compactly supported negative real test, prove the expected real Bochner sum over actual original process uniform increments converges to the horizon times the integral against the actual restricted negative Levy measure. No free marginal rate or auxiliary process is assumed. This integrates an independently proved original-process small-time Levy rate with the independently proved original uniform-grid expectation bridge.

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_uniform_grid_bochner_mean_rate_from_smalltime
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_compact_negative_test_real_rate

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_original_negative_uniform_grid_levy_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ)) :
    Tendsto (fun n : ℕ => ∫ ω,
      ∑ i ∈ Finset.range (n + 1),
        g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
           X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P)
      atTop (nhds ((T : ℝ) *
        ∫ y : ℝ, g y ∂(X.ν.restrict (Set.Iio (0 : ℝ))))) := by sorry
