-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_original_grid_mean_liminf_horizon_bound
-- name    : AvramDividend.Classical.avram_p2_34dbea70_actual_original_grid_mean_liminf_horizon_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:30:57.629203+00:00
-- url     : https://prove2.me/theorems/a1993f05-43c5-4a31-bed2-c972b7bd070d
-- title:
--   Original negative uniform-grid expected-count liminf is bounded by finite C times horizon
-- statement:
--   For the literal original spectrally negative Lévy X on its actual sample space and positive horizon T, the liminf of expected ENNReal sums of negative adjacent-grid increment indicators at threshold epsilon is bounded by a finite ENNReal.ofReal(C*T), with a positive real C. This transfers the accepted eventual uniform upper bound to the exact limit quantity required by the accepted Fatou expectation bridge, without assuming a compensator or Lévy-rate equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_original_grid_mean_horizon_uniform

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_actual_original_grid_mean_liminf_horizon_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      Filter.liminf (fun n : ℕ =>
        ∫⁻ ω, ∑ i ∈ Finset.range (n + 1),
          (Iic (-ε)).indicator (fun _ : ℝ => (1 : ℝ≥0∞))
            (X.X (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
              X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P) atTop ≤
        ENNReal.ofReal (C * (T : ℝ)) := by sorry
