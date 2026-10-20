-- Prove2me | Theorems.Thm_AvramDividend_Classical_laplace_origin_zero_of_normalised_small
-- name    : AvramDividend.Classical.laplace_origin_zero_of_normalised_small
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:57:10.867316+00:00
-- url     : https://prove2.me/theorems/09e071ab-2689-44a5-8687-c30ea15bfd77
-- title:
--   A nonnegative monotone scale-like Laplace transform vanishes at the origin when its normalised reciprocal exponent is arbitrarily small
-- statement:
--   Let W be nonnegative and nondecreasing on the nonnegative real axis and have positive-parameter Laplace transform (ψ(θ)-q)⁻¹. Assume θ(ψ(θ)-q)⁻¹ can be made arbitrarily small for admissible θ>0. Then W(0)=0. The proof uses W(x)≥W(0) for x>0 and ∫₀∞ exp(-θx)dx=1/θ to deduce W(0)≤θ(ψ(θ)-q)⁻¹, then contradiction. This is a useful Tauberian boundary lemma for Gaussian and infinite-variation scale-function branches, conditional only on the explicit normalised exponent bound.
-- source:
--   Kuznetsov Kyprianou Rivero 2012 Theory of Scale Functions, boundary behaviour under unbounded variation; pinned Mathlib integral_exp_mul_Ioi and integrableOn_exp_mul_Ioi.

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

open MeasureTheory Set
open scoped Topology

theorem AvramDividend.Classical.laplace_origin_zero_of_normalised_small
    (W ψ : ℝ → ℝ) (q β₀ : ℝ)
    (hW : ∀ x : ℝ, 0 ≤ x → 0 ≤ W x)
    (hmono : MonotoneOn W (Ici (0 : ℝ)))
    (hLap : ∀ θ : ℝ, β₀ ≤ θ → 0 < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * W x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * W x) =
        (ψ θ - q)⁻¹)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ θ : ℝ, β₀ ≤ θ ∧ 0 < θ ∧ θ * (ψ θ - q)⁻¹ < ε) :
    W 0 = 0 := by sorry
