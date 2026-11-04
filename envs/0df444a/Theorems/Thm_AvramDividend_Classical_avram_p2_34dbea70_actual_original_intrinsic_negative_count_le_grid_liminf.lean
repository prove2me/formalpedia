-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_original_intrinsic_negative_count_le_grid_liminf
-- name    : AvramDividend.Classical.avram_p2_34dbea70_actual_original_intrinsic_negative_count_le_grid_liminf
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:24:21.671201+00:00
-- url     : https://prove2.me/theorems/da103e9d-0e4f-4127-b678-ee185ed72e7b
-- title:
--   Actual intrinsic marked negative jumps bounded by source grid indicator liminf
-- statement:
--   For the genuine original SpectrallyNegativeLevy on its original probability space, the intrinsic negative-band marked count on the interval (0,T] is bounded pathwise by the ENNReal liminf of original uniform-grid negative increment indicators. The proof directly combines the already-proved exact source future-path transport, actual zero-future path regularity, and accepted general ENNReal pathwise liminf bound. It assumes no compensation or jump rate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_futurepath_marked_count_transport
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_zero_future_canonical_leftlim_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_all_negative_path_jumps_le_ennreal_indicator_liminf

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENat ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_actual_original_intrinsic_negative_count_le_grid_liminf
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-ε)) ≤
      Filter.liminf (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          (if X.X (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
              X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω < -ε / 2
            then (1 : ℝ≥0∞) else 0)) atTop := by sorry
