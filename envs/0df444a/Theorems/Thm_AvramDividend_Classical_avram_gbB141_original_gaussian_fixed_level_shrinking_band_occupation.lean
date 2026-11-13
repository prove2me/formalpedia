-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB141_original_gaussian_fixed_level_shrinking_band_occupation
-- name    : AvramDividend.Classical.avram_gbB141_original_gaussian_fixed_level_shrinking_band_occupation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T09:43:28.120197+00:00
-- url     : https://prove2.me/theorems/ab8bc576-7248-4d01-982f-bfab02826b13
-- title:
--   Original Gaussian fixed-level shrinking spatial-band occupation tends to zero
-- statement:
--   For the original unbounded-variation zero-jump Gaussian driver and the actual admissible dividend strategy, the Lebesgue time occupation of shrinking spatial bands about any fixed level b tends to zero on almost every path before rho, horizon n. This is the genuine stochastic local-time/occupation estimate. Together with the proved scalar B140 it implies original B100 fixed-level zero occupation.
-- source:
--   Original Gaussian stopped postpayment reserve and shrinking-band occupation estimates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB141_original_gaussian_fixed_level_shrinking_band_occupation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ =>
        volume {t : ℝ |
          0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
          abs (x + X.X (Real.toNNReal t) ω -
            rightLimit D (Real.toNNReal t) ω - b) <
              (1 : ℝ) / ((k : ℝ) + 1)})
        atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
