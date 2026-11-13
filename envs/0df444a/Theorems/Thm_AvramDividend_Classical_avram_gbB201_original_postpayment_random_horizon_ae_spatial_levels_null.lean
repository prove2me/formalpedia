-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB201_original_postpayment_random_horizon_ae_spatial_levels_null
-- name    : AvramDividend.Classical.avram_gbB201_original_postpayment_random_horizon_ae_spatial_levels_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:13:25.731178+00:00
-- url     : https://prove2.me/theorems/d5b760d6-ac57-435e-995f-a0f6898960cc
-- title:
--   Original postpayment reserve has null stopped occupation at almost every real clipping level
-- statement:
--   For any original dividend strategy and any possibly sample-dependent stopped horizon, for Lebesgue almost every spatial clipping level the level set of the original postpayment reserve has zero Lebesgue time occupation, simultaneously on an almost-sure event for that level.
-- source:
--   Gaussian B real-time clipped gradient convergence alternative: combined Proved B189 and B195; supports selecting legitimate non-atomic clipping levels for random stopping horizons, without assuming every fixed level is atomless.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB201_original_postpayment_random_horizon_ae_spatial_levels_null
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ y ∂(volume : Measure ℝ), ∀ᵐ ω ∂P,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω = y} = 0 := by sorry
