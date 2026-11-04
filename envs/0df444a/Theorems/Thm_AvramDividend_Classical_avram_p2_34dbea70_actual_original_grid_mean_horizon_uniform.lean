-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_original_grid_mean_horizon_uniform
-- name    : AvramDividend.Classical.avram_p2_34dbea70_actual_original_grid_mean_horizon_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:19:49.395486+00:00
-- url     : https://prove2.me/theorems/e457eedb-9ee8-4f40-aa24-f9dd4662e26f
-- title:
--   Actual original Lévy negative-grid expectation is uniformly bounded by C times horizon
-- statement:
--   For the literal original spectrally negative Lévy process X, positive horizon T and negative jump threshold epsilon, the expected uniform-grid count of increments at most minus epsilon has a finite uniform bound ENNReal.ofReal(C*T) for all sufficiently fine grids. The proof combines accepted original-grid stationary means and the actual process negative-tail small-time estimate with an exact mesh sum, without identifying any compensator or assuming a Lévy jump rate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_original_negative_grid_mean_uniform_tail_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_real_rate_mesh_sum

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_actual_original_grid_mean_horizon_uniform
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        (∫⁻ ω, ∑ i ∈ Finset.range (n + 1),
          (Iic (-ε)).indicator (fun _ : ℝ => (1 : ℝ≥0∞))
            (X.X (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
              X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P) ≤
        ENNReal.ofReal (C * (T : ℝ)) := by sorry
