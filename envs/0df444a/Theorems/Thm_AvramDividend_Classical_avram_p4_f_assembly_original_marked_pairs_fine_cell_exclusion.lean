-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_pairs_fine_cell_exclusion
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_marked_pairs_fine_cell_exclusion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:16:06.342363+00:00
-- url     : https://prove2.me/theorems/f6039862-12a3-4313-9c67-7cdbe46996bf
-- title:
--   Small enough original time-mesh cells contain no two chronological negative-band jumps
-- statement:
--   For the exact original spectrally negative Lévy finite negative-band marked-time set, there is one positive grid resolution k such that no real time interval (s,t] with scaled width k(t-s)≤T can contain two distinct ordered negative-band original source jump times. It is a source-exact pathwise finite-grid collision-exclusion lemma for refining original second factorial moments.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_pairs_uniform_grid_scale
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_marked_pairs_fine_cell_exclusion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ k : ℕ, 0 < k ∧
      ∀ u ∈ F, ∀ v ∈ F, u < v →
        ∀ s t : ℝ, s < (u : ℝ) → (v : ℝ) ≤ t →
          (k : ℝ) * (t - s) ≤ (T : ℝ) → False := by sorry
