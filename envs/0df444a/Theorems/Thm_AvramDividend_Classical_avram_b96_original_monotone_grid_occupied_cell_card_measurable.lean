-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b96_original_monotone_grid_occupied_cell_card_measurable
-- name    : AvramDividend.Classical.avram_b96_original_monotone_grid_occupied_cell_card_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T14:36:52.878249+00:00
-- url     : https://prove2.me/theorems/f7267486-df88-4f27-80f4-16cc1a919ee5
-- title:
--   Measurability of the exact original Poisson occupied-cell cardinal on a monotone finite grid
-- statement:
--   Use the Proved original-source measurable finite sum of indicators that an actual nonzero Levy source jump occurs in each monotone grid cell. Finset.card_filter identifies this indicator sum with the ENNReal cardinality of the occupied-cell Finset. This provides the measurability ingredient of the exact original physical marked-cell count required for the finite-activity mixed stopped Ito source energy estimate.
-- source:
--   Proved avram_bv_excess25_original_allnegative_occupied_grid_count_measurable and original SpectrallyNegativeLevy marks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess25_original_allnegative_occupied_grid_count_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The canonical source Poisson occupied-cell cardinal is measurable on a monotone grid. -/

theorem AvramDividend.Classical.avram_b96_original_monotone_grid_occupied_cell_card_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ) :
    Measurable (fun ω : Ω =>
      (((Finset.range m).filter (fun i =>
        ((Measure.count.restrict {t : ℝ≥0 |
            0 < t ∧ X.X t ω -
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
          (fun t : ℝ≥0 => (t, X.X t ω -
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
          (Ioc (u i) (u (i + 1)) ×ˢ (Set.univ : Set ℝ)) ≠ 0)).card : ℝ≥0∞)) := by sorry
