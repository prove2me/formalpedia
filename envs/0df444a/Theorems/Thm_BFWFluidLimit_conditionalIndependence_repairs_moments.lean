-- Prove2me | Theorems.Thm_BFWFluidLimit_conditionalIndependence_repairs_moments
-- name    : BFWFluidLimit.conditionalIndependence_repairs_moments
-- status  : Proved
-- author  : @wfe2017
-- created : 2026-11-20T11:13:09.301561+00:00
-- url     : https://prove2.me/theorems/ec4db4f0-e854-4774-82b8-589f6db67e79
-- title:
--   Current-price independence repairs exploration noise moments
-- statement:
--   Let F be the past information and G = F ∨ σ(P) include the full current price vector. Assume that every integrable measurable function of the current shock vector has the same conditional expectation given G and F, and each shock coordinate has conditional mean zero given F. If prices are bounded, then each shock coordinate has conditional mean zero given G, and each product P_i ε_i has conditional mean zero given F. This is the additional independence condition and its required consequence for the corrected version of BFW Theorem 3.1. No IID assumption on full observations or sub-Gaussian noise is used.
-- source:
--   J. Baek, V. F. Farias, F. Wu, Misspecified Estimate-then-Optimize Leads to Supra-Competitive Prices, arXiv:2605.16064v2, https://arxiv.org/pdf/2605.16064; Section 2.1 pp. 7–8 and Appendix F.3 pp. 46–48; explicit added conditional price/noise independence.

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Constructions.Pi
open MeasureTheory ProbabilityTheory

namespace BFWFluidLimit
theorem conditionalIndependence_repairs_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {N : ℕ} (F : MeasurableSpace Ω) (P E : Ω → Fin N → ℝ)
    (hG : F ⊔ MeasurableSpace.comap P inferInstance ≤ mΩ)
    (hind : ∀ φ : (Fin N → ℝ) → ℝ, Measurable φ → Integrable (φ ∘ E) μ →
      μ[φ ∘ E | F ⊔ MeasurableSpace.comap P inferInstance] =ᵐ[μ] μ[φ ∘ E | F])
    (hE : ∀ i, Integrable (fun ω => E ω i) μ)
    (hzero : ∀ i, μ[(fun ω => E ω i) | F] =ᵐ[μ] 0)
    (C : ℝ) (hbound : ∀ᵐ ω ∂μ, ∀ i, ‖P ω i‖ ≤ C) :
    ∀ i, (μ[(fun ω => E ω i) | F ⊔ MeasurableSpace.comap P inferInstance] =ᵐ[μ] 0) ∧
      (μ[(fun ω => P ω i * E ω i) | F] =ᵐ[μ] 0) := by sorry
end BFWFluidLimit
