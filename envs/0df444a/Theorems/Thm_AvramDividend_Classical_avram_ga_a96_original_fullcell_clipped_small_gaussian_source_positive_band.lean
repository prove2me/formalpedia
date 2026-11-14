-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a96_original_fullcell_clipped_small_gaussian_source_positive_band
-- name    : AvramDividend.Classical.avram_ga_a96_original_fullcell_clipped_small_gaussian_source_positive_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:22:43.807852+00:00
-- url     : https://prove2.me/theorems/9fa13db9-4fe0-497f-bb06-1f49669c0d90
-- title:
--   Actual clipped Gaussian physically full pre-stop small-source Taylor endpoint stays in original stopped positive compact reserve band almost surely
-- statement:
--   For the original dividend-controlled Gaussian source, every physically full pre-stop cell whose genuine raw Gaussian source displacement is sufficiently small has the exact clipped spatial Taylor endpoint inside a fixed positive compact reserve band almost surely.
-- source:
--   Direct b0d9951c actual clipped positive compact Gaussian full cell bridge to Proved ga_a75 and ga_a66, using ga_a63 and ga_a71.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a96_original_fullcell_clipped_small_gaussian_source_positive_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (j n m : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ᵐ ω ∂P, ∀ i : ℕ,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (ρ ω)
      s < ρ ω → s + Δ ≤ ρ ω →
      |X.X (s + Δ) ω - X.X s ω| ≤
        (1 : ℝ) / (2 * ((j : ℝ) + 1)) →
      (1 : ℝ) / (2 * ((j : ℝ) + 1)) ≤
        x + X.X (v (i + 1)) ω - rightLimit D (v i) ω ∧
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω ≤
        x + ((j : ℝ) + 1) +
          (1 : ℝ) / (2 * ((j : ℝ) + 1)) := by sorry
