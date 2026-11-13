-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB175_original_gaussian_controlled_localtime_density
-- name    : AvramDividend.Classical.avram_gbB175_original_gaussian_controlled_localtime_density
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T18:42:35.875949+00:00
-- url     : https://prove2.me/theorems/67710f0f-e626-4b25-bc0a-3316597b93c4
-- title:
--   Original controlled Gaussian stopped occupation admits bounded spatial local-time density
-- statement:
--   Existence of a globally finite-bounded spatial occupation density for the actual stopped controlled Gaussian reserve, with the time occupation of each band dominated by the corresponding spatial density integral. This is the substantive semimartingale local-time construction; the Gaussian coefficient is positive (B172) and the postpayment dividend path has finite variation (B173).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB175_original_gaussian_controlled_localtime_density
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ (ℓ : ℝ → ℝ≥0∞) (B : ℝ≥0),
      (∀ z : ℝ, ℓ z ≤ (B : ℝ≥0∞)) ∧
      ∀ (y ε : ℝ), 0 < ε → ε ≤ 1 →
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        abs (x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω - y) < ε} ≤
        ∫⁻ z in Ioo (y - ε) (y + ε), ℓ z ∂volume := by sorry
