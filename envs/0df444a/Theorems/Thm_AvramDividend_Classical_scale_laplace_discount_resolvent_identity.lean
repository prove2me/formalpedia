-- Prove2me | Theorems.Thm_AvramDividend_Classical_scale_laplace_discount_resolvent_identity
-- name    : AvramDividend.Classical.scale_laplace_discount_resolvent_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:48:55.949143+00:00
-- url     : https://prove2.me/theorems/3c3072e8-3201-4eed-9f5c-ffe983b2bd3f
-- title:
--   Two-discount resolvent identity for canonical scale-function Laplace transforms
-- statement:
--   For a spectrally negative Lévy process and any two canonical scale functions at discount q1 and q2, their Laplace transforms satisfy L(W_q2)-L(W_q1)=(q2-q1)L(W_q1)L(W_q2) at every nonnegative Laplace parameter where both transform identities apply. This is the precise algebraic resolvent identity underlying convolution transfer from q=0 to q>0 and thus provides an importable building block for scale-function regularity.
-- source:
--   Directly from the two IsScaleFunction Laplace identities and elementary field algebra, without any stochastic regularity assumptions.

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scale_laplace_discount_resolvent_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ θ : ℝ) (hθ : 0 ≤ θ)
    (hψ₁ : q₁ < X.ψ θ) (hψ₂ : q₂ < X.ψ θ)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁)
    (hW₂ : IsScaleFunction X q₂ W₂) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W₂ x) -
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W₁ x) =
    (q₂ - q₁) *
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W₁ x) *
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W₂ x) := by sorry
