-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_original_strict_grid_sum_measurable
-- name    : AvramDividend.Classical.avram_p2_34dbea70_actual_original_strict_grid_sum_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:42:56.388322+00:00
-- url     : https://prove2.me/theorems/efe1a084-51aa-4ddc-a650-803d30dff073
-- title:
--   Strict negative marked finite-grid sums are measurable on the actual original Lévy probability space
-- statement:
--   For every spectrally negative Lévy process on its original probability space, deterministic horizon and mesh, the finite ENNReal sum of strict negative-increment indicators is measurable. Measurability follows from the already proved original shifted-future coordinate-product measurability, cancellation of the common zero-time value, measurable strict real half-lines, and finite sums. This supplies the missing hypothesis of the genuine Fatou expected jump-count bridge without altering the source law or imposing a jump-rate hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_path_coordinate_product_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_actual_original_strict_grid_sum_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) (ε : ℝ) :
    Measurable (fun ω : Ω =>
      ∑ i ∈ Finset.range (n + 1),
        (if X.X (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
            X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω < -ε / 2
          then (1 : ℝ≥0∞) else 0)) := by sorry
