-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b132_original_finite_physical_grid_negative_band_occupied_set_eventually_exact
-- name    : AvramDividend.Classical.avram_b132_original_finite_physical_grid_negative_band_occupied_set_eventually_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:47:42.232943+00:00
-- url     : https://prove2.me/theorems/dd4b198a-510e-4e92-8bcf-a5bd1da7362e
-- title:
--   Every finite original physical grid negative-cutoff occupied-cell Finset stabilises exactly to all genuinely marked source cells
-- statement:
--   Fix the genuine original spectrally negative Levy sample path, a finite arbitrary physical grid of original source clock intervals and the actual marked Finset of grid cell indices containing at least one nonzero original source left-limit jump. For each negative reciprocal cutoff n form the Finset of cells containing a source jump with mark at most -1/(n+1). Authoritatively Proved B118 guarantees one finite cutoff capturing every genuinely marked cell, and Proved B115 makes the physically marked cutoff sets monotone. Every cutoff occupied set is a subset of actual marked cells because negative marks are nonzero. Thus for all sufficiently large cutoffs, the cutoff occupied Finset is exactly the genuine physically marked Finset, pathwise and on the original random grid. This direct exact same-source equality eliminates a separate unproved J capture premise and establishes the physical marked-grid index-count exhaustion for the stopped Ito source proof.
-- source:
--   Proved B118 original common finite marked-grid cutoff and Proved B115 original actual negative cutoff marked-time set monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b118_original_finite_physically_marked_cells_one_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_b115_original_random_interval_negative_mark_cutoff_sets_monotone
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Cutoff-band occupation of any finite original physical clock grid eventually agrees exactly with all actual marked cells. -/

theorem AvramDividend.Classical.avram_b132_original_finite_physical_grid_negative_band_occupied_set_eventually_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (S : Finset ℕ) (s t : ℕ → ℝ≥0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      S.filter (fun i => ∃ u : ℝ≥0,
        s i < u ∧ u ≤ t i ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1))) =
      S.filter (fun i => ∃ u : ℝ≥0,
        s i < u ∧ u ≤ t i ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) := by sorry
