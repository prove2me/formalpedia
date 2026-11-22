-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261122_original_stopped_source_given_bounded_levy_exponential_clock_calculus
-- name    : AvramDividend.Classical.avram_bridge20261122_original_stopped_source_given_bounded_levy_exponential_clock_calculus
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T22:28:01.566806+00:00
-- url     : https://prove2.me/theorems/046b6f16-b7d8-4835-b9b6-e02c60f56b39
-- title:
--   Physical stopped Ito source given proved bounded Levy exponential increment clock calculus
-- statement:
--   The physical original X,D,ruin-clipped right-continuous stopping clock and stopped Ito source reward are unchanged. Nine proved original-filtration stopped-Levy exponential semigroup and discount inequalities are available for bounded original-filtration stops, specialised to the same X,P. The Open child must still connect these to a legitimate physical localisation for the true right-continuous stop and establish the stochastic reward budget.
-- source:
--   Root-connected Open stopped Ito source 750ad13b with nine proved source export heads covering 10 bounded Levy exponential identities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bridge20261122_original_stopped_source_given_bounded_levy_exponential_clock_calculus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (hBoundedExpClock : (∀ (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (hh : 0 < h) (θ q : ℝ) (hθ : 0 ≤ θ)
    (hlt : q < X.ψ θ),
1 < ∫ ω, Real.exp (-(q * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P) ∧
      (∀ (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ) (hle : q ≤ X.ψ θ),
1 ≤ ∫ ω, Real.exp (-(q * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P) ∧
      (∀ (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (hh : 0 < h) (θ q : ℝ) (hθ : 0 ≤ θ)
    (hlt : X.ψ θ < q),
∫ ω, Real.exp (-(q * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P < 1) ∧
      (∀ (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h₁ h₂ : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ) (hle : h₁ ≤ h₂) (hψ : X.ψ θ ≤ q),
(∫ ω, Real.exp (-(q * (h₂ : ℝ))) *
        Real.exp (θ * (X.X (τ ω + h₂) ω - X.X (τ ω) ω)) ∂P) ≤
      ∫ ω, Real.exp (-(q * (h₁ : ℝ))) *
        Real.exp (θ * (X.X (τ ω + h₁) ω - X.X (τ ω) ω)) ∂P) ∧
      (∀ (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ q₁ q₂ : ℝ) (hθ : 0 ≤ θ) (hq : q₁ ≤ q₂),
(∫ ω, Real.exp (-(q₂ * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P) ≤
    ∫ ω, Real.exp (-(q₁ * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P) ∧
      (∀ (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h₁ h₂ : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ) (hle : h₁ ≤ h₂) (hψ : q ≤ X.ψ θ),
(∫ ω, Real.exp (-(q * (h₁ : ℝ))) *
        Real.exp (θ * (X.X (τ ω + h₁) ω - X.X (τ ω) ω)) ∂P) ≤
      ∫ ω, Real.exp (-(q * (h₂ : ℝ))) *
        Real.exp (θ * (X.X (τ ω + h₂) ω - X.X (τ ω) ω)) ∂P) ∧
      (∀ (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h k : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ),
∫ ω, Real.exp (-(q * ((h + k) : ℝ))) *
      Real.exp (θ * (X.X (τ ω + (h + k)) ω - X.X (τ ω) ω)) ∂P =
        Real.exp ((h : ℝ) * (X.ψ θ - q)) *
          Real.exp ((k : ℝ) * (X.ψ θ - q))) ∧
      (∀ (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ) (hcal : X.ψ θ = q),
∫ ω, Real.exp (-(q * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P = 1) ∧
      (∀ (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ) (hle : X.ψ θ ≤ q),
∫ ω, Real.exp (-(q * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P ≤ 1)) :
    ∃ W Cash Term M G H : Ω → ℝ,
      (∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
        else riskProcess X x D (τ ω) ω) ∧
      (∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) ∧
      (∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) ∧
      AEStronglyMeasurable Term P ∧
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by sorry
