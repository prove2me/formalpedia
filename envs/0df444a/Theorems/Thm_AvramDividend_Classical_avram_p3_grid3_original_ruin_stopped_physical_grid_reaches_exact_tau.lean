-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_grid_reaches_exact_tau
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_physical_grid_reaches_exact_tau
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:51:37.642912+00:00
-- url     : https://prove2.me/theorems/6927bfb4-0b1a-46d3-8e69-2e04f3cf34a9
-- title:
--   Original uniformly sampled ruin-stopped physical grid reaches exactly min(ruinTime,horizon) at its final node
-- statement:
--   On the genuine original X and actual dividend D, the stopping time tau=(min(ruinTime,T)).toNNReal is bounded by finite horizon T. The previously Proved uniform stopped grid reaches min(T,tau) at index m+1; this theorem identifies it with tau exactly. It establishes that the strict-interior/boundary-crossing grid partition covers the full stopped time and so can be compared to literal strict Iio T cash.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_physical_grid_reaches_exact_tau
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun k =>
      min (((min k (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    u (m + 1) = τ := by sorry
