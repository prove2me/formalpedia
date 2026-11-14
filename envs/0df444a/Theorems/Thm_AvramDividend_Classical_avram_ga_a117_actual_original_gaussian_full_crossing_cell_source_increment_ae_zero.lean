-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a117_actual_original_gaussian_full_crossing_cell_source_increment_ae_zero
-- name    : AvramDividend.Classical.avram_ga_a117_actual_original_gaussian_full_crossing_cell_source_increment_ae_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:56:21.425734+00:00
-- url     : https://prove2.me/theorems/ffb2208b-22c6-4fcc-a78b-fd0f13325665
-- title:
--   True original Gaussian full physical crossing source increment vanishes a.s. at an arbitrarily randomly selected grid index
-- statement:
--   For the original zero-jump Lévy process and any potentially random physical uniform grid index whose complete mesh cell lies inside the fixed horizon, the actual un-clipped Gaussian increment X(s_i+Delta)-X(s_i) tends to zero almost surely. It is the real compensated generator source increment on the stopped crossing cell, and its random index need not be deterministic or predictable.
-- source:
--   Proved original Gaussian random-clock uniform source continuity ga102; source-faithful full physical compensator of the genuine clipped crossing cell.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a117_actual_original_gaussian_full_crossing_cell_source_increment_ae_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (i : ℕ → Ω → ℕ)
    (hEnd : ∀ (m : ℕ) (ω : Ω),
      (i m ω : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) ≤ (n : ℝ≥0)) :
    ∀ᵐ ω ∂P, Tendsto (fun m =>
      X.X ((i m ω : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
      X.X ((i m ω : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω)
      atTop (𝓝 (0 : ℝ)) := by sorry
