-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
-- name    : AvramDividend.Classical.bv_esscher_root_subcritical_kernel_mass
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T13:00:16.711476+00:00
-- url     : https://prove2.me/theorems/3e5e114d-05a5-40a2-9e82-e0d3f81e2687
-- title:
--   At a positive BV Esscher root the discounted jump kernel is integrable and subcritical
-- statement:
--   For the original bounded-variation spectrally negative Lévy process, φ>0 solving ψφ=q>0 implies the nonnegative jump-magnitude discounted first moment is integrable and strictly less than the BV drift δ. The proof composes (i) Proved exponential jump integrability for θ≥0 on negative jumps; (ii) the positive jump-magnitude integrability transformation, published but pending proof; (iii) the generic discounted-moment integrability theorem; (iv) the Proved nonnegative-parameter exact BV exponent identity; (v) the Proved root-conditioned strict jump-mass inequality. This ties the model-specific renewal subcriticality directly to standing BV assumptions and eliminates extra integrability premises.
-- source:
--   Published and remote Proved Avram BV Lévy exponent, negative/positive magnitude integrability and Esscher subcriticality helpers.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_root_subcritical_kernel_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    Integrable
        (fun z : ℝ≥0 => (z : ℝ) * Real.exp (-(φ * (z : ℝ))))
        (X.ν.map (fun y : ℝ => Real.toNNReal (-y))) ∧
      (∫ z : ℝ≥0,
        (z : ℝ) * Real.exp (-(φ * (z : ℝ)))
        ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) < X.drift := by sorry
