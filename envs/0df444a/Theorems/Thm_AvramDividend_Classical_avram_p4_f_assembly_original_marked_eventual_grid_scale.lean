-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_eventual_grid_scale
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_marked_eventual_grid_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:21:53.292853+00:00
-- url     : https://prove2.me/theorems/9c43fe5d-7034-4a84-840e-b3390dad164e
-- title:
--   Every finer deterministic grid separates the same original negative-band marked jump pairs
-- statement:
--   For each original negative-band finite marked-time path, a single positive deterministic mesh scale k0 depending on the path guarantees that every finer positive integer mesh k≥k0 separates all distinct chronologically ordered original marked-time pairs. This strengthens the accepted one-grid scale to eventual uniform refinement, a genuine pathwise prerequisite for the original chronological second-factorial expectation; it assumes no stochastic moment, replacement Poisson law or new process.
-- source:
--   Accepted original-source finite marked-time uniform-grid scale d4f9ea74. Monotonicity of multiplication by the nonnegative time separation for k≥k0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_pairs_uniform_grid_scale
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_marked_eventual_grid_scale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ k₀ : ℕ, 0 < k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ∀ u ∈ F, ∀ v ∈ F, u < v →
          (T : ℝ) < (k : ℝ) * ((v : ℝ) - (u : ℝ)) := by sorry
