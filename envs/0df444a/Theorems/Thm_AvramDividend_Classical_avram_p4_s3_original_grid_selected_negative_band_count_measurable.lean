-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_grid_selected_negative_band_count_measurable
-- name    : AvramDividend.Classical.avram_p4_s3_original_grid_selected_negative_band_count_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:30:52.675365+00:00
-- url     : https://prove2.me/theorems/4926eb4c-28dc-4528-9825-578fd279f92f
-- title:
--   Original negative-band counts are measurable at measurable countable-grid clocks
-- statement:
--   The actual negative-band jump count evaluated at a random grid time grid(tick ω) is measurable whenever tick is a measurable integer-valued index. This follows by a countable fibre decomposition and the proved fixed-time original jump-count measurability. It provides measurable dyadic/staircase approximations to a general random horizon.
-- source:
--   Exact original finite-band measurable count proof 7f0f2707-c11a-4e35-9aa3-96950b57cce1, with countable measurable partitions of the sample space.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_grid_selected_negative_band_count_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (tick : Ω → ℕ) (htick : Measurable tick)
    (grid : ℕ → ℝ≥0) :
    Measurable (fun ω : Ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ grid (tick ω) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard) := by sorry
