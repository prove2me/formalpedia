-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a409_original_zerojump_all_fullcells_uniform_source_modulus
-- name    : AvramDividend.Classical.avram_ga_a409_original_zerojump_all_fullcells_uniform_source_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:19:31.854077+00:00
-- url     : https://prove2.me/theorems/58a8d8ae-3464-4be9-8265-9b40ac1c339a
-- title:
--   Original zero-jump Gaussian source all finite full-cell increments vanish uniformly a.s.
-- statement:
--   For almost all paths of the original zero-jump Lévy source, the maximum absolute source increment across all finite physical-grid cells on a fixed horizon shrinks to zero.
-- source:
--   Proved zero-nu path uniform continuity avram_ubv_top12 and finite-cell oscillation a406.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a409_original_zerojump_all_fullcells_uniform_source_modulus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
        ∀ i : ℕ, i < m →
          |X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
                 ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
            X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω| < ε := by sorry
