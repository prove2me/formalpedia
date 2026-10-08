-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_positive_magnitude_nonneg
-- name    : AvramDividend.Classical.bv_laplace_exponent_positive_magnitude_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T11:15:43.192439+00:00
-- url     : https://prove2.me/theorems/d9f634f2-9401-4b2c-8cdf-9ea75a15c587
-- title:
--   Exact BV jump-magnitude Laplace exponent identity for every nonnegative theta
-- statement:
--   Extend the already-Proved exact BV Lévy–Khintchine jump-magnitude identity from θ≥1 to all θ≥0. Obtain the exponential jump integrability from the new nonnegative-theta lemma, compensation integrability from the existing Proved lemma, apply the existing Proved BV Laplace-exponent rearrangement, and transport the negative-jump integral to positive magnitudes using the existing Proved pushforward formula. This generalization is required to evaluate the root equation ψ(φ)=q when 0<φ<1.
-- source:
--   Proved bv_laplace_exponent_positive_magnitude_exact, bv_laplace_exponent_rearrangement_of_integrable and negative_jump_magnitude_integral_transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_laplace_exponent_positive_magnitude_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    X.ψ θ = X.drift * θ -
      ∫ z : ℝ≥0, (1 - Real.exp (-θ * (z : ℝ)))
        ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))) := by sorry
