-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_fixed_kernel_scale_laplace_bridge
-- name    : AvramDividend.Classical.bv_esscher_fixed_kernel_scale_laplace_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:11:25.806439+00:00
-- url     : https://prove2.me/theorems/7918540b-5b46-4197-964f-e67c30f04503
-- title:
--   Fixed-kernel Esscher scale and geometric cumulative Laplace bridge
-- statement:
--   For an arbitrary specified subcritical Esscher kernel and finite-cumulative geometric renewal measure, convert the fixed-kernel denominator identity into equality of the real Laplace transforms of the tilted q-scale function and the cumulative renewal measure, preserving both witnesses.
-- source:
--   Proof adapted from accepted bv_esscher_explicit_geometric_scale_laplace (c390f500-f969-44c4-8e9f-cd648d71faf3) and the newly isolated fixed-kernel denominator lemma.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_esscher_fixed_kernel_denominator_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_lintegral
import Theorems.Thm_AvramDividend_Classical_positive_cumulative_laplace_real_integral_bridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Complex.Exponential

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_fixed_kernel_scale_laplace_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (φ : ℝ) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) (κ β : Measure ℝ) (hκsf : SFinite κ)
    (hκsupp : κ (Iio (0 : ℝ)) = 0)
    (hκmass : κ Set.univ < ENNReal.ofReal X.drift)
    (hκLap : ∀ s : ℝ, 0 < s →
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(s * z))) ∂κ) =
      (∫⁻ z : ℝ≥0, ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
        ENNReal.ofReal ((1 - Real.exp (-(s * (z : ℝ)))) / s)
        ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))))
    (hβlocal : ∀ x : ℝ, β (Iic x) ≠ ⊤)
    (hβLap : ∀ s : ℝ, 0 < s →
      (∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-s * x)) * β (Iic x)) =
      ENNReal.ofReal (1 / s) *
        ((ENNReal.ofReal X.drift)⁻¹ *
          (1 - (ENNReal.ofReal X.drift)⁻¹ *
            (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂κ))⁻¹)) :
    ∃ b : ℝ, ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
        (Real.exp (-(φ * x)) * W x)) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * (β (Iic x)).toReal) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
        (Real.exp (-(φ * x)) * W x)) =
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * (β (Iic x)).toReal) := by sorry
