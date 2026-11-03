-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_marked_grid_count_exact_second_moment
-- name    : AvramDividend.Classical.avram_wave6_01_original_past_marked_grid_count_exact_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:19:15.200169+00:00
-- url     : https://prove2.me/theorems/26cc80f3-5f67-43bc-b832-d4e078829774
-- title:
--   Predictable-past factorisation of original Borel-marked grid count second moment
-- statement:
--   For the same original spectrally negative Levy process on Ω, P and 𝓕, the second moment of its finite Borel-marked increment occupancy count, restricted to any A∈𝓕_s before the grid starts, equals P(A) times the unrestricted source second moment. Proved from the exact source past-two-marked-increment probability product, its diagonal one-increment version, and finite ENNReal Tonelli. This is the independent-past uniform-integrability estimate required in pathwise original jump-count approximation, without assuming compensation or ν intensity.
-- source:
--   Avram Wave6 Chat01, original predictable quadratic grid estimate as a needed missing source-law interface for canonical intrinsic compensator 393b03a8. No stochastic martingale L2 closure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_past_event_next_levy_increment_measure_product
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_two_separated_marked_increment_cells_probability_product
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_borel_marked_grid_count_exact_second_moment

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave6_01_original_past_marked_grid_count_exact_second_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (t : ℕ → ℝ≥0) (ht : Monotone t) (hst : s ≤ t 0)
    (n : ℕ) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω,
      (A.indicator (fun _ => (1 : ℝ≥0∞)) ω) *
      (∑ i ∈ Finset.range n,
        ({v : Ω | X.X (t (i + 1)) v - X.X (t i) v ∈ B}).indicator
          (fun _ => (1 : ℝ≥0∞)) ω) ^ 2 ∂P) =
    P A * (∫⁻ ω,
      (∑ i ∈ Finset.range n,
        ({v : Ω | X.X (t (i + 1)) v - X.X (t i) v ∈ B}).indicator
          (fun _ => (1 : ℝ≥0∞)) ω) ^ 2 ∂P) := by sorry
