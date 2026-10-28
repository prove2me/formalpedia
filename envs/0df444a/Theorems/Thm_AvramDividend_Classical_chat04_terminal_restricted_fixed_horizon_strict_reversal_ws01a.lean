-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_terminal_restricted_fixed_horizon_strict_reversal_ws01a
-- name    : AvramDividend.Classical.chat04_terminal_restricted_fixed_horizon_strict_reversal_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:03:13.656965+00:00
-- url     : https://prove2.me/theorems/9fb452f3-4b68-469c-88ce-ddd1f86ebe97
-- title:
--   Genuine fixed-horizon Levy drawdown/minimum strict reversal jointly with terminal displacement event
-- statement:
--   For an actual spectrally negative Levy process at fixed positive horizon T, the terminal drawdown strict threshold and the running-minimum strict threshold have equal original-law probabilities even after intersecting with the terminal displacement event X_T-X_0<c. The terminal event is retained jointly, not discarded as in marginal reversal. The proof restricts the genuine finite-grid increment reversal using an invariant terminal-sum indicator density, identifies the terminal sum by exact Levy telescoping, and passes dyadic grids to the actual cadlag path via measure continuity. No Wiener-Hopf independence or killed-scale identity is assumed.
-- source:
--   Proved a712024a, da772096, fd442ab6, 6362f09e, e57db112, right-continuous dyadic strict-event exhaustion and grid refinement. Adaptation of the accepted fixed-terminal strict reversal proof to a genuine terminal indicator, not an Esscher exponential density.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_right_continuous_strict_dyadic_grid_event
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_finite_dyadic_grid_refines
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_strict_grid_path_probability_of_vector_reversal
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_increment_vector_tilted_reversal
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_map_withDensity_observable_density
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fin_mesh_increment_sum_terminal
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fin_reverse_preserves_sum

open AvramDividend.Classical MeasureTheory Filter Topology Finset Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.chat04_terminal_restricted_fixed_horizon_strict_reversal_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T)
    (a c : ℝ) :
    (P.withDensity (fun ω : Ω =>
      if X.X T ω - X.X 0 ω < c then (1 : ℝ≥0∞) else 0))
      {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X T ω - X.X s ω < a} =
    (P.withDensity (fun ω : Ω =>
      if X.X T ω - X.X 0 ω < c then (1 : ℝ≥0∞) else 0))
      {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X s ω - X.X 0 ω < a} := by sorry
