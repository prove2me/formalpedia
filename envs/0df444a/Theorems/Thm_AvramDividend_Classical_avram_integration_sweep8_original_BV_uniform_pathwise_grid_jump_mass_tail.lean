-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_integration_sweep8_original_BV_uniform_pathwise_grid_jump_mass_tail
-- name    : AvramDividend.Classical.avram_integration_sweep8_original_BV_uniform_pathwise_grid_jump_mass_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:12:29.198214+00:00
-- url     : https://prove2.me/theorems/64379a7f-c54e-4c0d-955a-8c2291ee86ff
-- title:
--   Uniform full-measure original BV jump-grid atom-exclusion inequality for random grids
-- statement:
--   There is one original full-measure source event on which every sample-path-dependent strictly increasing finite grid with marked-time-avoiding cells obeys the actual negative-left-jump excluded-tail inequality, with the original X.X and finite horizon fixed.
-- source:
--   Uniform-in-s,t original source a.e. summability f0ec726b and cumulative additivity 50ef916b are moved before quantification over arbitrary grids, combined with original jump sign 561ccef5 and proved sweep7 combinatorial tail a333aff8. This fixes the quantifier-order gap of the independently Proved fixed-grid result and is needed for truly random stopping grids.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep7_disjoint_unmarked_jump_cells_tail
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_integration_sweep8_original_BV_uniform_pathwise_grid_jump_mass_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (cells : Finset ℕ)
      (marked : Finset ℝ≥0), StrictMono u →
      (∀ i ∈ cells, u (i + 1) ≤ T) →
      (∀ i ∈ cells, ∀ t ∈ marked,
        ¬ (u i < t ∧ t ≤ u (i + 1))) →
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) s - X.X s ω else 0
      let j : ℝ≥0 → ℝ := fun t =>
        if 0 < t ∧ t ≤ T then
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t - X.X t ω else 0
      Finset.sum cells (fun i => J (u (i + 1)) - J (u i)) ≤
        ∑' t : ℝ≥0, if t ∈ marked then 0 else j t := by sorry
