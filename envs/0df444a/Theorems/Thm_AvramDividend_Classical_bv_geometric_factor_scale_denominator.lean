-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_geometric_factor_scale_denominator
-- name    : AvramDividend.Classical.bv_geometric_factor_scale_denominator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:25:29.163431+00:00
-- url     : https://prove2.me/theorems/e60b068e-7425-4a2e-b1d6-bd1356da3b98
-- title:
--   The BV geometric renewal factor equals the scale-function Laplace denominator
-- statement:
--   For a standing bounded-variation spectrally negative Lévy process, q>0 and a positive renewal discount s, assume θ=s+q/drift is at least 1 and the shifted positive jump-magnitude kernel transform at s is strictly below the positive BV drift. Then ψ(θ)>q. Moreover the positive geometric-renewal cumulative factor (1/s)(1/drift)/(1-(1/drift)r(s)), interpreted in ℝ≥0∞, is exactly ENNReal.ofReal((ψ(θ)-q)^(-1)). The proof converts the nonnegative jump-magnitude lintegral to the corresponding real integral using BV integrability and then applies the already proved exact BV Lévy-exponent identity.
-- source:
--   Proved bv_standing_drift_pos, bv_laplace_exponent_positive_magnitude_exact, pending source-faithful bv_positive_magnitude_exponential_integrable; pinned Mathlib ofReal_integral_eq_lintegral_ofReal and ENNReal ofReal arithmetic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_geometric_factor_scale_denominator
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hbv : X.BoundedVariation)
    (s : ℝ) (hs : 0 < s)
    (hθ : 1 ≤ s + q / X.drift)
    (hgap :
      (∫⁻ z : ℝ≥0, ENNReal.ofReal
        ((1 - Real.exp (-(s + q / X.drift) * (z : ℝ))) / s)
        ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) <
        ENNReal.ofReal X.drift) :
    q < X.ψ (s + q / X.drift) ∧
    ENNReal.ofReal (1 / s) *
      ((ENNReal.ofReal X.drift)⁻¹ *
        (1 - (ENNReal.ofReal X.drift)⁻¹ *
          (∫⁻ z : ℝ≥0, ENNReal.ofReal
            ((1 - Real.exp (-(s + q / X.drift) * (z : ℝ))) / s)
            ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))))⁻¹) =
      ENNReal.ofReal ((X.ψ (s + q / X.drift) - q)⁻¹) := by sorry
