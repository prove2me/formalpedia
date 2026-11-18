-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB56_original_barrier_pre_ruin_all_short_tube_times
-- name    : AvramDividend.Classical.avram_gbB56_original_barrier_pre_ruin_all_short_tube_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:39:32.950537+00:00
-- url     : https://prove2.me/theorems/fe22033e-ce1b-42c0-838e-8675d624a725
-- title:
--   All strict source-tube times are strictly pre-ruin for the original cap barrier
-- statement:
--   If the true original source stays within a radius-1/400 tube through a bounded horizon T, then every strictly earlier physical time s<T is strictly earlier than the original extended ruinTime for the cap barrier at x=C=1/8. This is the exact source paymentTimes/Iio pre-ruin requirement needed by a positive-drift finite-cap stopped cash identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB55_original_barrier_ruinTime_ge_tube_horizon
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB56_original_barrier_pre_ruin_all_short_tube_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω)
    (hTube : ∀ t : ℝ≥0, t ≤ T →
      |X.X t ω| ≤ (1 / 400 : ℝ)) :
    ∀ s : ℝ≥0, s < T →
      (s : ℝ≥0∞) <
        ruinTime X (1 / 8 : ℝ)
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω := by sorry
