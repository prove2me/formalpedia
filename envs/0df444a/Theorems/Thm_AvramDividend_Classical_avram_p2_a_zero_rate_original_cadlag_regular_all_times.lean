-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_cadlag_regular_all_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:09:51.62565+00:00
-- url     : https://prove2.me/theorems/09e1699b-750b-49bf-934c-43e6db86a2dd
-- title:
--   Original Lévy path supplies grid left-limit and right-continuity at every time
-- statement:
--   Extract the exact source path hypotheses needed by the full-grid compact-test jump-limit theorem. At each positive time use the original X.leftLim and pinned tendsto_leftLim_of_tendsto; at zero the strict-left filter is bottom; use original X.rightCont at every time for right continuity. Holds for every original sample, independent of bounded/unbounded variation.

import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.LeftRightNhds
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_cadlag_regular_all_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    (∀ t : ℝ≥0,
      Tendsto (fun u : ℝ≥0 => X.X u ω) (𝓝[<] t)
        (𝓝 (Function.leftLim (fun u : ℝ≥0 => X.X u ω) t))) ∧
    (∀ t : ℝ≥0,
      ContinuousWithinAt (fun u : ℝ≥0 => X.X u ω) (Ici t) t) := by sorry
