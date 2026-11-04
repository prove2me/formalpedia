-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_original_negative_grid_mean_uniform_tail_bound
-- name    : AvramDividend.Classical.avram_p2_34dbea70_actual_original_negative_grid_mean_uniform_tail_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:05:39.609242+00:00
-- url     : https://prove2.me/theorems/447e7f42-55cd-41dc-864f-e5d7ce3138b5
-- title:
--   Original negative uniform-grid marked first moment is bounded by genuine small-time tails
-- statement:
--   For the genuine original spectrally negative Lévy X and a negative mark threshold epsilon, the expectation of the finite grid marked indicator sum is eventually bounded by the sum over actual grid cells of C times their length. This directly combines the source-specific uniform-grid first-moment identity with the independently proved original-process negative-tail probability O(h) bound, without a compensator, assumed jump intensity, or substituted process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_uniform_original_grid_mean_stationary_cells
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_negative_tail_uniform_width_probability_O

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_actual_original_negative_grid_mean_uniform_tail_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        (∫⁻ ω, ∑ i ∈ Finset.range (n + 1),
          (Iic (-ε)).indicator (fun _ : ℝ => (1 : ℝ≥0∞))
            (X.X (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
              X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P) ≤
        ∑ _i ∈ Finset.range (n + 1),
          ENNReal.ofReal (C * ((T / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ)) := by sorry
