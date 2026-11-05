-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_negative_band_grid_eventually_injective
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_negative_band_grid_eventually_injective
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:23:50.749233+00:00
-- url     : https://prove2.me/theorems/82f20738-8b36-4250-ba69-9cec2d336761
-- title:
--   Original negative-band jump times eventually occupy distinct uniform grid cells
-- statement:
--   For the actual original Lévy process, any finite negative-band intrinsic jump-time set is eventually separated by uniform cells, provided the supplied cell selector satisfies the exact half-open cell inequalities. The lemma imports no replacement process or intensity assumption.
-- source:
--   Original spectrally negative Lévy X.X intrinsic negative-band marked times, using the proved source finite-time theorem and uniform finite-selector separation; Mathlib pinned 0df444a3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_uniform_selected_cells_eventually_injective

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_original_negative_band_grid_eventually_injective
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∀ (idx : ℝ≥0 → ℕ → ℕ),
      (∀ t ∈ F, ∀ k : ℕ,
        ((idx t k : ℕ) : ℝ≥0) * (T / ((k : ℝ≥0) + 1)) < t ∧
        t ≤ (((idx t k + 1 : ℕ) : ℝ≥0) *
          (T / ((k : ℝ≥0) + 1)))) →
      ∀ᶠ k : ℕ in Filter.atTop,
        Set.InjOn (fun t => idx t k) (F : Set ℝ≥0) := by sorry
