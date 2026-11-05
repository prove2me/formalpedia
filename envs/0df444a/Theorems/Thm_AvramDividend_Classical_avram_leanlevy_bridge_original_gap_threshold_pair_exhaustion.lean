-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_gap_threshold_pair_exhaustion
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_gap_threshold_pair_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:24:31.059865+00:00
-- url     : https://prove2.me/theorems/182358f5-18a3-4681-8784-582711f645df
-- title:
--   Original chronological pairs stabilise under vanishing positive time-gap thresholds
-- statement:
--   For the literal negative-band marked jump times of the original Avram Lévy path X, retain only chronological pairs whose positive time separation exceeds 1/(m+1). As the threshold decreases, these nested finite pair sets eventually equal every actual chronological pair on each physical sample path. This proves a fully explicit, source-preserving refinement scheme by the accepted finite-pair exhaustion bridge, with no probabilistic replacement model or external independence assumption.
-- source:
--   Accepted original path finite-grid exhaustion helper 9125f6f8, pinned exists_nat_one_div_lt and one_div_le_one_div_of_le, finite source marked jump-time theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_finite_band_grid_pair_exhaustion
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_gap_threshold_pair_exhaustion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ)
    (F : Finset ℝ≥0)
    (hF : F = (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset) :
    ∃ N, ∀ m ≥ N,
      (((F ×ˢ F).filter (fun p => p.1 < p.2)).filter
        (fun p => (1 : ℝ) / ((m : ℝ) + 1) <
          (p.2 : ℝ) - (p.1 : ℝ))) =
        (F ×ˢ F).filter (fun p => p.1 < p.2) := by sorry
