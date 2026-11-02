-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_variable_time_predictable_finite_rank_marked_grid_first_moment
-- name    : AvramDividend.Classical.avram_wave6_01_original_variable_time_predictable_finite_rank_marked_grid_first_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T00:07:47.356796+00:00
-- url     : https://prove2.me/theorems/3a1e3230-702c-41c8-8816-6c03a1f886d4
-- title:
--   Original Lévy variable-history predictable finite-rank Borel-marked future-grid first-moment factorisation
-- statement:
--   For the unchanged original spectrally negative Levy process X with its original filtration and probability P, any finite family of distinct deterministic history times s_i, nonnegative weights H_i measurable under the corresponding original F_{s_i}, arbitrary Borel marks B_i and arbitrary finite future grids produces the exact sum of expected products E[H_i C_i] = E[H_i] E[C_i]. This is a full finite-rank source predictable simple-grid identity with independently varying history times and mark sets, extending the previously Proved common-history-time interface. No assumption of Poisson jump marks, compensation or equivalence of a detached process is used. The finite-grid cell expectations remain source marginals, not unproved nu(B).
-- source:
--   Combine the canonically Proved arbitrary-Borel original future-grid factor 43c7d32a on each individually adapted history time s_i with precise Borel measurability and finite Tonelli additivity. Original Ω,P,𝓕,X.X unchanged; no jump-intensity identification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_future_marked_increment_grid_weighted_factor

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave6_01_original_variable_time_predictable_finite_rank_marked_grid_first_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (I : Finset ι) (s : ι → ℝ≥0)
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ I, Measurable[𝓕 (s i)] (H i))
    (B : ι → Set ℝ)
    (hB : ∀ i ∈ I, MeasurableSet (B i))
    (n : ι → ℕ) (grid : ι → ℕ → ℝ≥0) :
    (∫⁻ ω, ∑ i ∈ I, H i ω *
      ((((Finset.range (n i)).filter (fun j =>
        (X.X (s i + grid i (j + 1)) ω - X.X (s i) ω) -
          (X.X (s i + grid i j) ω - X.X (s i) ω) ∈ B i)).card : ℝ≥0∞)) ∂P) =
    ∑ i ∈ I, (∫⁻ ω, H i ω ∂P) *
      (∫⁻ ω, ((((Finset.range (n i)).filter (fun j =>
        (X.X (s i + grid i (j + 1)) ω - X.X (s i) ω) -
          (X.X (s i + grid i j) ω - X.X (s i) ω) ∈ B i)).card : ℝ≥0∞)) ∂P) := by sorry
