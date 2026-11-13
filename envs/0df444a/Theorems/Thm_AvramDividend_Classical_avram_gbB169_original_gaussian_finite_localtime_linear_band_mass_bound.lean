-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB169_original_gaussian_finite_localtime_linear_band_mass_bound
-- name    : AvramDividend.Classical.avram_gbB169_original_gaussian_finite_localtime_linear_band_mass_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T17:21:56.922059+00:00
-- url     : https://prove2.me/theorems/9b4cc74e-6b74-4844-a05e-eb0dec05e595
-- title:
--   Original controlled Gaussian reserve has finite local-time band-mass bound
-- statement:
--   Uniform finite local-time bound: the actual controlled Gaussian reserve occupation mass in each shrinking band is at most L times its radius for some finite path-dependent L. This strengthening of B141 retains the exact process and strategy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB169_original_gaussian_finite_localtime_linear_band_mass_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ L : ℝ≥0, ∀ k : ℕ,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        abs (x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω - b) <
            (1 : ℝ) / ((k : ℝ) + 1)} ≤
        ENNReal.ofReal ((L : ℝ) / ((k : ℝ) + 1)) := by sorry
