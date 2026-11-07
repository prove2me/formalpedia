-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_scale_exponential_upper_envelope
-- name    : AvramDividend.Classical.avram_p4_f6_gaussian_scale_exponential_upper_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:08:28.122284+00:00
-- url     : https://prove2.me/theorems/b114eb46-8d6f-4bb4-8f44-70039cfbfb7f
-- title:
--   Global exponential envelope for q-scale functions with nonzero Gaussian volatility
-- statement:
--   For a spectrally negative Lévy process with positive Gaussian volatility and an arbitrary real discount q, every q-scale function W is globally bounded above by K exp(θy) for some θ,K≥0. This combines the proved superlinearity of the Lévy Laplace exponent with the proved globally bounded exponential damped q-scale function.
-- source:
--   Proved source c1392cb2 for ψ superlinearity and b9952447 for exponentially damped q-scale norm bound. This exact consequence is needed for the stopped killed two-sided exit comparison route to unrestricted HJB supersolution growth 51922c24.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_psi_superlinear_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_weighted_norm_bddAbove
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_f6_gaussian_scale_exponential_upper_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, W y ≤ K * Real.exp (θ * y) := by sorry
