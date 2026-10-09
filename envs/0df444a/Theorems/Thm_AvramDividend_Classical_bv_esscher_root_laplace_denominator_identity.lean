-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_root_laplace_denominator_identity
-- name    : AvramDividend.Classical.bv_esscher_root_laplace_denominator_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T16:27:47.162313+00:00
-- url     : https://prove2.me/theorems/e38154cd-6088-4aea-8551-60ffb7a01fae
-- title:
--   BV Esscher-root scale denominator equals drift less discounted jump compensator
-- statement:
--   In the BV spectrally negative Lévy model, for a positive root φ satisfying ψφ=q and any s>0, ψ(φ+s)-q equals δs minus the positive jump integral ∫e^(-φz)(1-e^(-sz))ν_mag(dz). Compose the Proved exact BV Lévy–Khintchine formula valid for every θ≥0, the Proved positive-magnitude compensator integrability, and the accepted difference-integral theorem for J(φ+s)-J(φ). This exact denominator identity is the missing deterministic translation from the Esscher discounted jump-tail kernel's geometric transform to the q-scale Laplace transform.
-- source:
--   Accepted bv_laplace_exponent_positive_magnitude_nonneg, positive_magnitude_compensator_integrable and esscher_jump_compensator_difference_integral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_root_laplace_denominator_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ s : ℝ) (hφ : 0 < φ) (hs : 0 < s)
    (hroot : X.ψ φ = q) :
    X.ψ (φ + s) - q =
      X.drift * s -
        (∫ z : ℝ≥0,
          Real.exp (-(φ * (z : ℝ))) *
            (1 - Real.exp (-(s * (z : ℝ))))
        ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) := by sorry
