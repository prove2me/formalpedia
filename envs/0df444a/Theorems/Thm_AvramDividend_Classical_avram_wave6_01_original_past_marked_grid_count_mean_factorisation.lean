-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_marked_grid_count_mean_factorisation
-- name    : AvramDividend.Classical.avram_wave6_01_original_past_marked_grid_count_mean_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:56:16.340197+00:00
-- url     : https://prove2.me/theorems/9a0220c9-a4f9-44df-96c8-43bb45a52688
-- title:
--   Original-past predictable marked-increment grid count mean factorisation
-- statement:
--   For any event A measurable at source time s, any monotone deterministic grid starting at or after s, and any Borel increment-mark set B, the original-space expectation of the product of 1_A and the finite count of B-marked source increments equals P(A) times the sum of actual original one-cell B-mark probabilities. This is a first-moment finite-grid predictable-step identity on the given Ω, P, 𝓕, X. It uses source independent increments but does not assume a jump compensator or identify those one-cell probabilities with X.ν.
-- source:
--   Avram Wave6 Chat01. Finite source-grid predictable marked event first moment from canonically Proved chat04_past_event_next_levy_increment_measure_product, original adaptation and finite ENNReal linearity; explicit bridge towards target source jump-count compensation 393b03a8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_past_event_next_levy_increment_measure_product

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave6_01_original_past_marked_grid_count_mean_factorisation
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
          (fun _ => (1 : ℝ≥0∞)) ω) ∂P) =
    P A * (∑ i ∈ Finset.range n,
      P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B}) := by sorry
