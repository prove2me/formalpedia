-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_Brownian_minus_two_Poisson_one_step_mean_identification
-- name    : AvramDividend.Classical.avram_jump6_A_original_Brownian_minus_two_Poisson_one_step_mean_identification
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:35:38.657507+00:00
-- url     : https://prove2.me/theorems/adf37027-36fb-4598-8e80-17fde7b94487
-- title:
--   Actual original Brownian minus two rate-one Poisson unit-time mean equals negative two
-- statement:
--   On the genuine original spectrally negative Lévy model X1=B1−2N1, when the actual integrable centred Brownian value has expectation zero and the integrable unit-rate Poisson mark count has expectation one, the exact original one-step Lévy mean ∫X1 dP is −2. This discharges the previously explicit mean premise in the Proved original intrinsic Gaussian and Jfull physical identification d0f2ccc6, closing a missing physical model-source interface.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_Brownian_minus_two_Poisson_one_step_mean_identification
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B N : Ω → ℝ)
    (hPath : ∀ ω, X.X 1 ω = B ω - 2 * N ω)
    (hBI : Integrable B P) (hNI : Integrable N P)
    (hBmean : (∫ ω, B ω ∂P) = (0 : ℝ))
    (hNmean : (∫ ω, N ω ∂P) = (1 : ℝ)) :
    (∫ ω, X.X 1 ω ∂P) = (-2 : ℝ) := by sorry
