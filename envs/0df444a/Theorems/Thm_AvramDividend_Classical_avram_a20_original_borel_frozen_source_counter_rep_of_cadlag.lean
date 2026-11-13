-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_frozen_source_counter_rep_of_cadlag
-- name    : AvramDividend.Classical.avram_a20_original_borel_frozen_source_counter_rep_of_cadlag
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T11:17:36.140813+00:00
-- url     : https://prove2.me/theorems/11e5e018-809e-44dc-ac81-b3f100248695
-- title:
--   Original arbitrary Borel marked source count factors through a measurable frozen càdlàg prefix
-- statement:
--   For the literal original spectrally negative Lévy process and any measurable Borel jump mark set B, the physical count in time (0,T] has a coordinate-product measurable functional of the source path stopped at deterministic horizon T. Establish its pathwise identity through the Proved actual jump-count encard formula, the Proved frozen prefix left-limit identity and the Proved generic Borel càdlàg jump-count measurable extractor. This extends the earlier Proved cutoff-specific frozen counter to arbitrary Borel marks, and supplies a source-adaptedness bridge for independent past/future marked counts.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_leftLim_before_stop

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Real original-path marked counts factor through a measurable frozen-prefix functional. -/

theorem AvramDividend.Classical.avram_a20_original_borel_frozen_source_counter_rep_of_cadlag
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B)
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
        (Ioc 0 T ×ˢ B) =
        F (fun v : ℝ≥0 => X.X (min v T) ω) := by sorry
