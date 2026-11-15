-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a76_finite_negative_activity_levy_gaussian_jump_exponent_split_20261114
-- name    : AvramDividend.Classical.avram_a76_finite_negative_activity_levy_gaussian_jump_exponent_split_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:15:31.825206+00:00
-- url     : https://prove2.me/theorems/e340db25-3882-45bf-a039-008e5420d42c
-- title:
--   Original general finite-negative-activity Lévy exponent separates exact Gaussian variance and un-compensated marked Poisson jump integral
-- statement:
--   For the actual spectrally negative Levy process, with finite negative-jump mass and arbitrary Gaussian coefficient, express its positive Laplace exponent as deterministic drift c theta, Gaussian contribution sigma squared theta squared /2, finite negative-mark compound Poisson exponential deficit integral and the original small-jump compensator drift. This identity follows from the Lévy-Khintchine definition, the deterministic original indicator integral A73, the compensated integral linearity A74, and the finite negative-activity exponential integrability A75. It is the precise exponent cancellation needed to prove the negative physical jump total Laplace law A72.
-- source:
--   Definition of SpectrallyNegativeLevy.ψ, proved/general A74 compensated negative exponential integral split and A75 finite negative Lévy exponential integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a76_finite_negative_activity_levy_gaussian_jump_exponent_split_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    X.ψ θ =
      X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
        (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν) -
        θ * (∫ y in Ioo (-1 : ℝ) 0, y ∂X.ν) := by sorry
