-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_frozen_source_counter_rep_of_cadlag
-- name    : AvramDividend.Classical.avram_wave7_06_original_negative_band_frozen_source_counter_rep_of_cadlag
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:41:45.291381+00:00
-- url     : https://prove2.me/theorems/22ce6bf4-84f6-441e-b812-1132a57cd292
-- title:
--   Original negative-band count is a measurable frozen-path functional under actual stopped càdlàg regularity
-- statement:
--   Given the exact original spectrally negative Lévy process X and the càdlàg regularity of its deterministic frozen paths, the original intrinsic negative-band jump count on (0,T] factors pointwise through a globally measurable functional F applied only to the path prefix frozen at T. This establishes the precise source-locality representation required for raw-filtration past-void measurability.
-- source:
--   W7-06 original-process compensated L²/L¹ bridge. Uses Proved original rectangle encard, frozen-prefix leftLim identity, and universal càdlàg marked-counter measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_leftLim_before_stop
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_negative_band_frozen_source_counter_rep_of_cadlag
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (hCad : ∀ ω : Ω,
      (∀ u : ℝ≥0, ContinuousWithinAt
        (fun v : ℝ≥0 => X.X (min v T) ω) (Ici u) u) ∧
      (∀ u : ℝ≥0, 0 < u →
        ∃ l : ℝ, Tendsto (fun v : ℝ≥0 => X.X (min v T) ω)
          (𝓝[<] u) (𝓝 l))) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧ ∀ ω : Ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) =
        F (fun v : ℝ≥0 => X.X (min v T) ω) := by sorry
