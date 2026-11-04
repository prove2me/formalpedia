-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_normalised_laplace_identity
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_normalised_laplace_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:36:22.625538+00:00
-- url     : https://prove2.me/theorems/dec049b5-9a92-4c38-b2ec-5d5953d5d0a4
-- title:
--   Original same-volatility zero-jump Levy normalised Gaussian marginal Laplace transform
-- statement:
--   For the same-source zero-jump Levy process Y with Gaussian coefficient equal to the original X and positive sigma, the positive Laplace transform of its drift-centred normalised fixed-time marginal equals exp(t theta squared over two). This is a verifiable Brownian-law prerequisite, not a pathwise Brownian or Itô theorem.
-- source:
--   Original SpectrallyNegativeLevy source triplet and previously Proved centred Laplace identity, Avram Palmowski Pistorius section 2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_centered_laplace_identity
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_normalised_laplace_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hν : Y.ν = 0) (hσeq : Y.σ = X.σ) (hσ : 0 < X.σ)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp
       (θ * ((Y.X t ω - (t : ℝ) * Y.c) / X.σ)) ∂P) =
      Real.exp ((t : ℝ) * (θ ^ 2 / 2)) := by sorry
