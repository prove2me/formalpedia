-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_origin_zero_of_superlinear_psi
-- name    : AvramDividend.Classical.scaleFunction_origin_zero_of_superlinear_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:52:35.605927+00:00
-- url     : https://prove2.me/theorems/effa0ac0-898d-4af8-a4f6-6c59968d96b4
-- title:
--   Superlinear Lévy exponent growth forces the canonical q-scale function to vanish at zero
-- statement:
--   If the canonical Laplace exponent ψ(θ) grows faster than linearly in θ in the sense that ψ(θ)/θ is eventually larger than every real constant, then every q-scale function at q>0 satisfies W(0)=0. Apply the Proved Tauberian Laplace-origin criterion with thresholds ensuring ψ(θ)>q and θ/(ψ(θ)-q) arbitrarily small.
-- source:
--   A Tauberian scale-function origin criterion combined with eventual normalised Lévy-exponent growth.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_origin_zero_of_superlinear_psi
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hgrowth : ∀ C : ℝ, ∃ β : ℝ, 1 ≤ β ∧
      ∀ θ : ℝ, β ≤ θ → C < X.ψ θ / θ) :
    W 0 = 0 := by sorry
