-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_origin_zero_of_quadratic_psi
-- name    : AvramDividend.Classical.scaleFunction_origin_zero_of_quadratic_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:23:29.263864+00:00
-- url     : https://prove2.me/theorems/a6b29c5d-655a-4dd3-bd00-d485a53128a3
-- title:
--   A canonical q-scale function vanishes at zero when its exponent has eventual quadratic growth
-- statement:
--   Given an exact q-scale function with continuous monotone positive support and Laplace transform 1/(ψ(θ)-q), an eventual positive quadratic exponent bound implies its origin value is zero. Uses the already Proved Laplace-origin lemma and the scalar normalized-reciprocal growth argument. Requires no Standing integrability.
-- source:
--   Tauberian Laplace-origin criterion combined with positive quadratic Lévy exponent coercivity; auxiliary analytic theorem normalized_reciprocal_small_of_quadratic_lower.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_origin_zero_of_quadratic_psi
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a β : ℝ) (ha : 0 < a)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hquad : ∀ θ : ℝ, β ≤ θ → a * θ ^ 2 ≤ X.ψ θ - q) :
    W 0 = 0 := by sorry
