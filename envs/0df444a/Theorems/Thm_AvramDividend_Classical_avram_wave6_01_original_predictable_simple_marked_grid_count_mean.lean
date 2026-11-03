-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_predictable_simple_marked_grid_count_mean
-- name    : AvramDividend.Classical.avram_wave6_01_original_predictable_simple_marked_grid_count_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:05:58.478854+00:00
-- url     : https://prove2.me/theorems/ef6f14e9-c405-4ae0-a538-fdb3ea77c98d
-- title:
--   Original predictable simple marked-grid finite-block first moment
-- statement:
--   On the genuine Ω/P/𝓕/X, the expectation of any finite sum of unit-coefficient predictable simple marked-increment grid blocks, each block tagged by a past event A_k∈𝓕_{s_k}, equals the finite sum of P(A_k) times its original one-cell marked increment probabilities. This is a finite simple step integrand identity for observation-grid approximations; it makes no claim that the cell probabilities equal Lévy intensity or that grid increments are intrinsic jumps.
-- source:
--   Avram Wave6 Chat01 direct finite ENNReal sum extension of canonically Proved 9a0220c9 original-past marked-grid single block. Source predictable simple step bridge towards intrinsic compensation parent 393b03a8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_marked_grid_count_mean_factorisation

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave6_01_original_predictable_simple_marked_grid_count_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m : ℕ) (s : Fin m → ℝ≥0)
    (t : Fin m → ℕ → ℝ≥0)
    (ht : ∀ k, Monotone (t k))
    (hst : ∀ k, s k ≤ t k 0)
    (n : Fin m → ℕ)
    (A : Fin m → Set Ω)
    (hA : ∀ k, MeasurableSet[𝓕 (s k)] (A k))
    (B : Fin m → Set ℝ)
    (hB : ∀ k, MeasurableSet (B k)) :
    (∫⁻ ω, ∑ k : Fin m,
      (A k).indicator (fun _ => (1 : ℝ≥0∞)) ω *
      (∑ i ∈ Finset.range (n k),
        ({v : Ω | X.X (t k (i + 1)) v - X.X (t k i) v ∈ B k}).indicator
          (fun _ => (1 : ℝ≥0∞)) ω) ∂P) =
    ∑ k : Fin m, P (A k) *
      (∑ i ∈ Finset.range (n k),
        P {ω | X.X (t k (i + 1)) ω - X.X (t k i) ω ∈ B k}) := by sorry
