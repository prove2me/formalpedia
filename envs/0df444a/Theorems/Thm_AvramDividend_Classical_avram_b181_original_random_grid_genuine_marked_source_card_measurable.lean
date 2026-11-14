-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b181_original_random_grid_genuine_marked_source_card_measurable
-- name    : AvramDividend.Classical.avram_b181_original_random_grid_genuine_marked_source_card_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:17:11.948929+00:00
-- url     : https://prove2.me/theorems/b0d88d85-b003-4f80-a23d-b769b72ac4c0
-- title:
--   Original genuinely jump-containing random grid has measurable finite marked-cell cardinal
-- statement:
--   For the genuine original spectrally negative Levy source on a finite random physical grid with measurable ordered endpoints, the number of cells containing an actual nonzero source jump is a measurable real random variable. A true jump implies that not all negative Poisson cutoff counts vanish by Proved B125. Conversely, a nonzero negative-band source count produces an actual negative physical source jump by Proved B179. The exactly equivalent cutoff-selected cardinal is measurable by B180. This directly supplies the source-faithful hJmeas required by stopped Gaussian/negative-jump energy verification.
-- source:
--   Proved B125, B179, and public B180 once Proved, no post-ruin continuation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b180_original_random_grid_any_negative_cutoff_occupied_card_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b125_original_all_zero_poisson_cutoff_counts_imply_true_jumpfree
import Theorems.Thm_AvramDividend_Classical_avram_b179_original_actual_negative_band_source_jump_iff_poisson_count_nonzero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b181_original_random_grid_genuine_marked_source_card_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (hs : ∀ i, Measurable (s i)) (ht : ∀ i, Measurable (t i))
    (hOrder : ∀ ω i, s i ω ≤ t i ω) :
    let J : Ω → Finset ℕ := fun ω => by
      classical
      exact S.filter (fun i => ∃ u : ℝ≥0, s i ω < u ∧ u ≤ t i ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    Measurable (fun ω => ((J ω).card : ℝ)) := by sorry
