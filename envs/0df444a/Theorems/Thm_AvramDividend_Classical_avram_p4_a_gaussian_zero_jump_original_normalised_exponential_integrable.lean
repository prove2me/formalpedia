-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_normalised_exponential_integrable
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_normalised_exponential_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:38:36.085386+00:00
-- url     : https://prove2.me/theorems/a42b9169-b3a4-4b1a-970d-6b170022186a
-- title:
--   Original same-volatility zero-jump Levy normalised positive MGF is finite
-- statement:
--   For an actual zero-jump Levy component whose Gaussian variance matches the original source X, positive exponential moments of its drift-centred normalised process are finite at fixed times. This is an exact integrability prerequisite for identifying standard Gaussian marginal laws, not an assumed Brownian process.
-- source:
--   Original SpectrallyNegativeLevy.laplace and now Proved centred exponential integrability helper, Avram Palmowski Pistorius section 2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_centered_exponential_integrable
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_normalised_exponential_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hν : Y.ν = 0) (hσeq : Y.σ = X.σ) (hσ : 0 < X.σ)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp
      (θ * ((Y.X t ω - (t : ℝ) * Y.c) / X.σ))) P := by sorry
