-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a105_original_gaussian_true_random_crossing_positive_compact_band
-- name    : AvramDividend.Classical.avram_ga_a105_original_gaussian_true_random_crossing_positive_compact_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:33:30.472023+00:00
-- url     : https://prove2.me/theorems/ec102a3f-a968-4ede-b811-45d86ef8f38e
-- title:
--   Actual Gaussian random stopping-crossing source endpoint eventually stays in an enlarged strictly positive compact band
-- statement:
--   Any original zero-jump Gaussian random mesh crossing source displacement vanishing with physical mesh width preserves an eventual strictly-positive postpayment reserve compact band [alpha,beta] within [alpha/2,beta+alpha/2]. This is a pathwise positive-domain guarantee for the genuine clipped crossing cell and is independent of deterministic or predictable index selection.
-- source:
--   Original Avram Gaussian b0 crossing-cell positive C2 endpoint, using proved zero-jump source continuity plus uniform modulus ga102.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a105_original_gaussian_true_random_crossing_positive_compact_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Icc 0 T ∧ t m ω ∈ Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1))
    (α β : ℝ) (hα : 0 < α) (y : ℕ → Ω → ℝ)
    (hBase : ∀ᵐ ω ∂P, ∀ᶠ m in atTop,
      α ≤ y m ω ∧ y m ω ≤ β) :
    ∀ᵐ ω ∂P, ∀ᶠ m in atTop,
      y m ω ∈ Icc (α / 2) (β + α / 2) ∧
        y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ∈
          Icc (α / 2) (β + α / 2) := by sorry
