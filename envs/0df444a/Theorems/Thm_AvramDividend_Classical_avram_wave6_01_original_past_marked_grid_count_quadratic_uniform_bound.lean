-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_marked_grid_count_quadratic_uniform_bound
-- name    : AvramDividend.Classical.avram_wave6_01_original_past_marked_grid_count_quadratic_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:42:42.973754+00:00
-- url     : https://prove2.me/theorems/e89c3d9c-57f7-4f70-acf7-a9ad9e36a8e6
-- title:
--   Source-past Borel-marked grid quadratic mass controlled by actual finite-grid event intensity
-- statement:
--   For a genuine spectrally negative Levy process on its given Omega, P, and filtration, and a past event A measurable at time s before the marked grid, the second moment of the original future Borel-marked increment occupancy count restricted to A is at most P(A) times mu+mu squared, where mu is the sum of the actual original increment-mark probabilities. The source-past exact second-moment factorisation and unconditional pairwise independent-grid bound jointly give a conditional uniform integrability estimate without assuming any jump measure compensation or Poisson proxy.
-- source:
--   Avram Wave6 Chat01, genuinely missing original predictable-past quadratic grid estimate for the intrinsic jump-count limiting argument to target 393b03a8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_marked_grid_count_exact_second_moment
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_borel_marked_grid_count_second_moment_upper_bound

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave6_01_original_past_marked_grid_count_quadratic_uniform_bound
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
          (fun _ => (1 : ℝ≥0∞)) ω) ^ 2 ∂P) ≤
    P A * ((∑ i ∈ Finset.range n,
      P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B}) +
      (∑ i ∈ Finset.range n,
      P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B}) ^ 2) := by sorry
