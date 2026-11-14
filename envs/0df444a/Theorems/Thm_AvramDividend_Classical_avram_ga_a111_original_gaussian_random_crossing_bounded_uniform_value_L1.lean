-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a111_original_gaussian_random_crossing_bounded_uniform_value_L1
-- name    : AvramDividend.Classical.avram_ga_a111_original_gaussian_random_crossing_bounded_uniform_value_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:40:20.765956+00:00
-- url     : https://prove2.me/theorems/1a7344f3-a04b-4aea-8442-56fa11a008b1
-- title:
--   Bounded uniformly continuous compact-truncated value on an actual random Gaussian crossing source has vanishing expected absolute L1 increment
-- statement:
--   For the actual original zero-jump Gaussian Lévy source, arbitrary randomly selected physical mesh crossing clocks yield a source increment converging to zero almost surely. Any bounded uniformly continuous real-valued function, in particular the original value clipped to a positive compact interval, has a spatial increment converging in expected absolute L1 by deterministic bounded domination. The reserve base may vary arbitrarily; the crossing index need not be predictable.
-- source:
--   Proved original random crossing source uniform continuity ga102 and pinned Mathlib dominated convergence, with the bounded compact-truncation route for b0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a111_original_gaussian_random_crossing_bounded_uniform_value_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Icc 0 T ∧ t m ω ∈ Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1))
    (w : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hW : ∀ z : ℝ, |w z| ≤ M)
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, |v - u| < δ → |w v - w u| < ε)
    (y : ℕ → Ω → ℝ)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      |w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)|) P) :
    Tendsto (fun m => ∫ ω,
      |w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)| ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
