-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_borel_marked_grid_mean_sum_of_stationary_cell_probabilities
-- name    : AvramDividend.Classical.avram_wave6_01_original_borel_marked_grid_mean_sum_of_stationary_cell_probabilities
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T00:01:28.64683+00:00
-- url     : https://prove2.me/theorems/20fc3267-08c7-4ed8-8f76-a424e35cdea6
-- title:
--   Actual Lévy Borel-marked finite-grid first moment equals the sum of stationary one-time cell probabilities
-- statement:
--   For the genuine spectrally negative Levy process X on its original probability space and every monotone finite deterministic grid, the expected finite Borel-mark occupancy sum of actual source increments is exactly the sum of probabilities that the genuine original one-time X at each cell duration falls in B. This is an exact source-law reduction using finite nonnegative Tonelli and the stationaryIncrements axiom, not a conditional compensation assumption. It supplies the marginal probability expression to which a genuine small-time Levy measure limit can later be applied, before pathwise approximation identifies the intrinsic marked source jump measure.
-- source:
--   The actual source stationaryIncrements field of SpectrallyNegativeLevy, IdentDistrib.measure_mem_eq for measurable B, indicator-one lintegral, finite Tonelli. No proxy, no ν(B) identification, no replacement filtration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave6_01_original_borel_marked_grid_mean_sum_of_stationary_cell_probabilities
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (n : ℕ) (grid : ℕ → ℝ≥0)
    (hGrid : ∀ i : ℕ, i < n → grid i ≤ grid (i + 1))
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ∑ i ∈ Finset.range n,
      B.indicator (fun _ : ℝ => (1 : ℝ≥0∞))
        (X.X (s + grid (i + 1)) ω - X.X (s + grid i) ω) ∂P) =
    ∑ i ∈ Finset.range n,
      P {ω : Ω | X.X ((s + grid (i + 1)) - (s + grid i)) ω ∈ B} := by sorry
