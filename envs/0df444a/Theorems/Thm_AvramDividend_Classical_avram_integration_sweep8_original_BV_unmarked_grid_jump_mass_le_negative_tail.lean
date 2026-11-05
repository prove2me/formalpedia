-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_integration_sweep8_original_BV_unmarked_grid_jump_mass_le_negative_tail
-- name    : AvramDividend.Classical.avram_integration_sweep8_original_BV_unmarked_grid_jump_mass_le_negative_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:08:31.792507+00:00
-- url     : https://prove2.me/theorems/0b3e02d8-e70c-455e-b1dd-298be64078b2
-- title:
--   Original BV Levy negative-jump unmarked grid mass bounded by true excluded source tail
-- statement:
--   For the actual spectrally negative Levy path X.X on a finite horizon, any finite family of disjoint strictly increasing genuine grid intervals whose endpoints stay before T and whose cells avoid marked source jump times has total raw negative-left-jump mass at most the original jump series excluding those marks, almost surely. Summability, nonnegativity and interval additivity come from existing Proved original-process results, while strict grid monotonicity supplies unique half-open membership.
-- source:
--   Original-process exact source summability f0ec726b-b68a-4a0f-a3b3-86166ccd2bfd, no-positive-left-jump 561ccef5-08ed-4169-b930-9bd8544810a6, cumulative interval additivity 50ef916b-57ed-4bdd-b0fa-5630d6e42904 and Proved sweep7 finite disjoint marked tail a333aff8-f975-497b-bd23-538e9c6be129. This discharges the original source cell-versus-atom tail after P3-F/P3-G construct finite marked-time avoidance. It does not establish the stopped C1 grid limit or martingale compensation.

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

theorem AvramDividend.Classical.avram_integration_sweep8_original_BV_unmarked_grid_jump_mass_le_negative_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (u : ℕ → ℝ≥0) (cells : Finset ℕ)
    (marked : Finset ℝ≥0) (hu : StrictMono u)
    (hBound : ∀ i ∈ cells, u (i + 1) ≤ T)
    (hAvoid : ∀ i ∈ cells, ∀ t ∈ marked,
      ¬ (u i < t ∧ t ≤ u (i + 1))) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) s - X.X s ω else 0
      let j : ℝ≥0 → ℝ := fun t =>
        if 0 < t ∧ t ≤ T then
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t - X.X t ω else 0
      Finset.sum cells (fun i => J (u (i + 1)) - J (u i)) ≤
        ∑' t : ℝ≥0, if t ∈ marked then 0 else j t := by sorry
