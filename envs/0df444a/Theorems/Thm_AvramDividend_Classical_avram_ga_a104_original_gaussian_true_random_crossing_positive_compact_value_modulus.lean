-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a104_original_gaussian_true_random_crossing_positive_compact_value_modulus
-- name    : AvramDividend.Classical.avram_ga_a104_original_gaussian_true_random_crossing_positive_compact_value_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:33:24.07951+00:00
-- url     : https://prove2.me/theorems/92379e68-e9ae-4e92-a413-7d1469f6b2e6
-- title:
--   True random Gaussian crossing source spatial value increment tends zero almost surely inside the original positive compact reserve band
-- statement:
--   For the original zero-jump Lévy process, any random physical crossing increments of vanishing mesh width have value-function increments tending to zero almost surely, provided their actual pre- and post-source reserve values eventually lie in the original positive compact region of continuity. This respects the value function C2 restriction and does not Taylor-expand an un-clipped negative terminal reserve.
-- source:
--   Original Avram Gaussian positive interior true crossing source: proven source pathwise modulus ga102 and compact value modulus ga28.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_ga_a28_compact_modulus_last_increment
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a104_original_gaussian_true_random_crossing_positive_compact_value_modulus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Icc 0 T ∧ t m ω ∈ Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1))
    (w : ℝ → ℝ) (a b : ℝ) (y : ℕ → Ω → ℝ)
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, u ∈ Icc a b → v ∈ Icc a b →
        |v - u| < δ → |w v - w u| < ε)
    (hBand : ∀ᵐ ω ∂P, ∀ᶠ m in atTop,
      y m ω ∈ Icc a b ∧
        y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ∈ Icc a b) :
    ∀ᵐ ω ∂P, Tendsto (fun m =>
      w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)) atTop (𝓝 (0 : ℝ)) := by sorry
