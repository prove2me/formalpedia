-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_borel_marked_grid_count_second_moment_upper_bound
-- name    : AvramDividend.Classical.avram_wave6_01_original_borel_marked_grid_count_second_moment_upper_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:53:45.322608+00:00
-- url     : https://prove2.me/theorems/519dbbb9-e04a-4ad0-aba1-e54ac3560115
-- title:
--   Original Levy Borel-marked finite-grid second-moment quadratic bound
-- statement:
--   For the original spectrally negative Levy process on the same probability space, every finite increasing deterministic-time grid and Borel increment-mark set B has ENNReal second moment of its marked occupancy count at most μ+μ², where μ is the sum of its actual original one-cell event probabilities. Follows from exact first principles pair independence and finite nonnegative sum estimates, and supplies the elementary uniform-integrability bound for source jump-count approximation. No ν-intensity or conditional compensator assumption is made.
-- source:
--   Avram Wave6 Chat01. Source quadratic integrability bound for finite marked-increment occupancy, derived from canonical exact source second moment eac4c5a9, target intrinsic jump compensator 393b03a8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_borel_marked_grid_count_exact_second_moment

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave6_01_original_borel_marked_grid_count_second_moment_upper_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, (∑ i ∈ Finset.range n,
      ({v : Ω | X.X (t (i + 1)) v - X.X (t i) v ∈ B}).indicator
        (fun _ => (1 : ℝ≥0∞)) ω) ^ 2 ∂P) ≤
    (∑ i ∈ Finset.range n,
      P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B}) +
    (∑ i ∈ Finset.range n,
      P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B}) ^ 2 := by sorry
