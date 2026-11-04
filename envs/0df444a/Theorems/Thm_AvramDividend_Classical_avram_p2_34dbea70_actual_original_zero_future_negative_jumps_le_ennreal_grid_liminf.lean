-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_original_zero_future_negative_jumps_le_ennreal_grid_liminf
-- name    : AvramDividend.Classical.avram_p2_34dbea70_actual_original_zero_future_negative_jumps_le_ennreal_grid_liminf
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:12:10.525745+00:00
-- url     : https://prove2.me/theorems/85fd866a-cce7-4384-9aa6-e8fe06951c7c
-- title:
--   Actual original zero-future Lévy negative jump count obeys the ENNReal grid liminf bound
-- statement:
--   For the actual original SpectrallyNegativeLevy source X and original sample omega, any Y definitionally equal to the genuine zero-future increment path X.X u omega - X.X 0 omega satisfies an ENNReal all-negative-jump count liminf bound by the exact adjacent uniform-grid increment indicators at threshold epsilon/2. The proof uses the accepted source path right-continuity/canonical strict-left-limit bridge and the accepted all-jump ENNReal grid liminf result, with no rate, compensator, finite-activity, BV or replacement-process assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_zero_future_canonical_leftlim_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_all_negative_path_jumps_le_ennreal_indicator_liminf

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENat ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_actual_original_zero_future_negative_jumps_le_ennreal_grid_liminf
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε)
    (Y : ℝ≥0 → ℝ) (hY : Y = fun u => X.X u ω - X.X 0 ω) :
    ENat.toENNReal ({u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      Y u - Function.leftLim Y u ≠ 0 ∧
      Y u - Function.leftLim Y u ∈ Iic (-ε)}).encard ≤
      Filter.liminf (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          (if Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
              Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) < -ε / 2
            then (1 : ℝ≥0∞) else 0)) atTop := by sorry
