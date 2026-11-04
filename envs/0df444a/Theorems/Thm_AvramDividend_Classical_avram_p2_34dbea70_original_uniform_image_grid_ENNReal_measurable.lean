-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_uniform_image_grid_ENNReal_measurable
-- name    : AvramDividend.Classical.avram_p2_34dbea70_original_uniform_image_grid_ENNReal_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:47:05.851325+00:00
-- url     : https://prove2.me/theorems/f42dc934-64ee-43e2-b741-68d931b11890
-- title:
--   Original Lévy negative uniform endpoint-image jump count is samplewise measurable
-- statement:
--   For the exact original spectrally negative Lévy process X on its given probability space, all deterministic horizon T, uniform resolution n and negative threshold epsilon, the ENNReal cast of the finite cardinality of marked endpoint-image grid cells is a measurable function of the original sample omega. This supplies the actual grid-count measurability prerequisite of the original negative-band Fatou envelope, using the original future-coordinate measurability theorem and finite marked-filter count measurability, with no rate or Poisson assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_path_coordinate_product_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_finite_measurable_marked_filter_card_ENNReal

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_p2_34dbea70_original_uniform_image_grid_ENNReal_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (ε : ℝ) :
    Measurable (fun ω : Ω => (((((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
      (fun t : ℝ≥0 => X.X t ω -
        X.X (t - (T / ((n : ℝ≥0) + 1))) ω < -ε / 2)).card : ℕ∞) : ℝ≥0∞)) := by sorry
