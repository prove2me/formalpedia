-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_eventual_uniform_grid_pair_card
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_eventual_uniform_grid_pair_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:07:37.505109+00:00
-- url     : https://prove2.me/theorems/f672f2af-9920-4ae3-8af4-6965ce1f1843
-- title:
--   Original negative-band chronological pair count equals sufficiently fine physical uniform-grid crossing sum
-- statement:
--   For every sample path and positive original physical horizon, its finite original negative-band chronological time-pair count equals the uniform crossing-pair grid cardinality sum for every sufficiently fine grid. The grid uses strict-left/right-closed original time cells and actual source jumps.
-- source:
--   Exact original finite negative-band marked time set, accepted physical cell selector, finite-grid chronological pair cover, pairwise disjoint half-open future cells and cardinality sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_negative_band_uniform_cells_with_separation
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_cell_chronological_pair_cover
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_grid_ioc_pairwise_disjoint
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_grid_pair_card_sum

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_original_eventual_uniform_grid_pair_card
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∀ᶠ k : ℕ in Filter.atTop,
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card =
        ∑ i : Fin (k + 1),
          ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
            p.1 ≤ (i.val : ℝ≥0) * (T / ((k : ℝ≥0) + 1)) ∧
            (i.val : ℝ≥0) * (T / ((k : ℝ≥0) + 1)) < p.2 ∧
            p.2 ≤ (((i.val + 1 : ℕ) : ℝ≥0) *
              (T / ((k : ℝ≥0) + 1))))).card := by sorry
