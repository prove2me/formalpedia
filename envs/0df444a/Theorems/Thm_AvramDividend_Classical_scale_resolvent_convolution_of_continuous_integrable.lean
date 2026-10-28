-- Prove2me | Theorems.Thm_AvramDividend_Classical_scale_resolvent_convolution_of_continuous_integrable
-- name    : AvramDividend.Classical.scale_resolvent_convolution_of_continuous_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:55:34.427994+00:00
-- url     : https://prove2.me/theorems/5b9b0974-3f30-45d5-bcf2-e68e3cce2a83
-- title:
--   Real-space two-discount scale resolvent identity from continuous integrable convolution
-- statement:
--   The standard scale-function resolvent convolution equation holds on the positive axis whenever the causal convolution is continuous and its Laplace transform integrable on a common exponential half-line. The proof combines the two-discount rational Laplace identity, an already proved positive convolution-transform theorem, and an already proved uniqueness theorem for continuous functions. This is an analytic bridge toward transferring scale regularity from q=0 to positive discount.
-- source:
--   Uses the proved scale_laplace_discount_resolvent_identity (3c3072e8-3201-4eed-9f5c-ffe983b2bd3f), positive_causal_convolution_laplace_product (5473ec27-7b9c-42dc-aa29-72c87f745b48), and continuousOn_Ioi_eq_of_laplace_eq_signed (83290951-5903-4855-9932-c1d5eb47c2e8).

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scale_resolvent_convolution_of_continuous_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ b : ℝ)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁)
    (hW₂ : IsScaleFunction X q₂ W₂)
    (hlarge : ∀ θ : ℝ, b < θ →
      0 ≤ θ ∧ q₁ < X.ψ θ ∧ q₂ < X.ψ θ)
    (hKcont : ContinuousOn
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s))
      (Ioi (0 : ℝ)))
    (hKint : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)))
        (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 < x →
      W₂ x = W₁ x + (q₂ - q₁) *
        (∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)) := by sorry
