-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_psi_above_of_gap_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_psi_above_of_gap_no_standing_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T05:44:53.293489+00:00
-- url     : https://prove2.me/theorems/165056e3-5713-4ca7-b1f8-35c27e253fee
-- title:
--   Laplace gap inequalities force psi above q at all large theta
-- statement:
--   Given the J/q/B gap inequalities at index N, monotonicity of J, positivity of q and bounded variation, the Laplace exponent exceeds q at every θ≥(N:ℝ)+1, with no Standing assumption. Helper D3b isolating the per-theta psi-above argument; with D1/D2/D3a it discharges child p2m81_bv_driftpos_eventual_psi_above_no_standing_public.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.p2m81_bv_psi_above_of_gap_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (N : ℕ)
    (hJN : (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))) - (((X.c + (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))))) / 4) < (∫ y : ℝ, (Real.exp (((N : ℝ) + 1) * y) - 1 - ((N : ℝ) + 1) * y) / ((N : ℝ) + 1) ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))))
    (hqN : q / ((N : ℝ) + 1) < (((X.c + (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))))) / 4))
    (hBN : (∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν) / ((N : ℝ) + 1) < (((X.c + (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))))) / 4))
    (hmono : ∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ ≤ θ₂ → (∫ y : ℝ, (Real.exp (θ₁ * y) - 1 - θ₁ * y) / θ₁ ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))) ≤ (∫ y : ℝ, (Real.exp (θ₂ * y) - 1 - θ₂ * y) / θ₂ ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))))
    (hBV : X.BoundedVariation) :
    ∀ θ : ℝ, ((N : ℝ) + 1) ≤ θ → q < X.ψ θ := by sorry
