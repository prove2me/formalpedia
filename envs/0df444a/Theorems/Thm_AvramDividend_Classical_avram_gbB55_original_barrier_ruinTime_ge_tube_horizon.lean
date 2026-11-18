-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB55_original_barrier_ruinTime_ge_tube_horizon
-- name    : AvramDividend.Classical.avram_gbB55_original_barrier_ruinTime_ge_tube_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:31:14.575244+00:00
-- url     : https://prove2.me/theorems/0125521a-94f8-4f4e-9c7f-b1a014e4a106
-- title:
--   Original cap barrier ruin time is at least the positive narrow-source-tube horizon
-- statement:
--   For the actual original SpectrallyNegativeLevy riskProcess and cap barrier at x=C=1/8, a uniformly narrow source-path tube through T keeps the risk reserve above b=5/44 and hence strictly positive on the entire interval [0,T]. Since the original ruinTime is the infimum of times with negative reserves, its extended stopping time cannot be earlier than T. This proves the original pre-ruin requirement on the Gaussian tube.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB55_original_barrier_ruinTime_ge_tube_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω)
    (hTube : ∀ t : ℝ≥0, t ≤ T →
      |X.X t ω| ≤ (1 / 400 : ℝ)) :
    (T : ℝ≥0∞) ≤
      ruinTime X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω := by sorry
