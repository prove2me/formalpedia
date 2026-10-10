-- Prove2me | Theorems.Thm_DRSOWass_Duality_lemma_4_iii
-- name    : DRSOWass.Duality.lemma_4_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:28:47.680535+00:00
-- url     : https://prove2.me/theorems/95ba6340-1206-41cf-a47e-67cc1088a9e4
-- title:
--   Lemma 4(iii) — one-sided derivatives of Φ(·,ζ) are bounded by D̄ and D̲
-- statement:
--   Let $(\Xi,d)$ be a Polish space, $p\in[1,\infty)$, $\nu$ a Borel probability measure, $\Psi\in L^1(\nu)$ Borel measurable, with $\kappa<\infty$. Then there is a $\nu$-measurable set $B$ with $\nu(B)=1$ such that:
--
--   1. for all $\lambda>\kappa$ and $\zeta\in B$ the left partial derivative $\partial\Phi(\lambda,\zeta)/\partial\lambda-$ exists (as a real number) and
--   $$\overline D(\lambda,\zeta)\le\frac{\partial\Phi(\lambda,\zeta)}{\partial\lambda-}\le\lim_{\lambda_1\uparrow\lambda}\underline D(\lambda_1,\zeta);$$
--   2. for all $\lambda\ge0$ and every $\zeta\in\Xi$ with $\Phi(\lambda,\zeta)>-\infty$ the right partial derivative $\partial\Phi(\lambda,\zeta)/\partial\lambda+$ exists in $(-\infty,\infty]$ and
--   $$\lim_{\lambda_2\downarrow\lambda}\overline D(\lambda_2,\zeta)\le\frac{\partial\Phi(\lambda,\zeta)}{\partial\lambda+}\le\underline D(\lambda,\zeta).$$
--
--   The derivatives of the dual integrand in $\lambda$ are thus sandwiched between the extreme transport distances of near-optimal points, which is what links dual optimality conditions to primal feasibility.
--
--   **Formalization Note** $\Phi(\cdot,\zeta)$ is finite on $(\lambda,\infty)$ whenever $\Phi(\lambda,\zeta)>-\infty$, so the right difference quotients are real; their limit is taken in $[-\infty,\infty]$ because at $\lambda=\kappa$ it can be $+\infty$ (bounded only by $\underline D(\kappa,\zeta)$). The one-sided limits of the nonincreasing functions $\underline D(\cdot,\zeta)$, $\overline D(\cdot,\zeta)$ are written as the infimum of $\underline D(\lambda_1,\zeta)$ over $\lambda_1\in(\kappa,\lambda)$ and the supremum of $\overline D(\lambda_2,\zeta)$ over $\lambda_2>\lambda$. Part 1 and Lemma 4(i) each carry their own full-measure set $B$ (their intersection serves both). Borel measurability of $\Psi$ is added, as in p. 5.
-- source:
--   Gao, Kleywegt, Distributionally Robust Stochastic Optimization with Wasserstein Distance, arXiv:1604.02199v3, pp. 10–11, Lemma 4(iii)

import Mathlib
import Definitions.Def_DRSOWass_Duality_Setting

open MeasureTheory Filter Topology

namespace DRSOWass.Duality

/-- Lemma 4(iii) (Derivative), p. 11, for `κ < ∞`: there is `B ∈ B_ν(Ξ)` with `ν(B) = 1` such
that for `λ > κ` and `ζ ∈ B` the left derivative `L` of `Φ(·, ζ)` at `λ` exists (finite) and
`D̄(λ, ζ) ≤ L ≤ lim_{λ₁ ↑ λ} D̲(λ₁, ζ)`; and for `λ ≥ 0` and every `ζ` with `Φ(λ, ζ) > −∞` the
right derivative `R ∈ (−∞, ∞]` exists and `lim_{λ₂ ↓ λ} D̄(λ₂, ζ) ≤ R ≤ D̲(λ, ζ)`. The one-sided
limits of the monotone functions `D̲(·, ζ)`, `D̄(·, ζ)` are written as an infimum over
`λ₁ ∈ (κ, λ)` and a supremum over `λ₂ > λ`. -/
theorem lemma_4_iii {Ξ : Type*} [MetricSpace Ξ] [CompleteSpace Ξ] [SecondCountableTopology Ξ]
    [MeasurableSpace Ξ] [BorelSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (Ψ : Ξ → ℝ) (p : ℝ)
    (hp : 1 ≤ p) (hΨm : Measurable Ψ) (hΨ : Integrable Ψ ν)
    (hκ : growthRate Ψ ν p < ⊤) :
    ∃ B : Set Ξ, NullMeasurableSet B ν ∧ ν Bᶜ = 0 ∧
      (∀ lam : ℝ, growthRate Ψ ν p < ENNReal.ofReal lam → ∀ ζ ∈ B,
        ∃ L : ℝ, HasDerivWithinAt (fun l : ℝ => (Phi Ψ p l ζ).toReal) L (Set.Iio lam) lam ∧
          ((DUpper Ψ p lam ζ : ENNReal) : EReal) ≤ (L : EReal) ∧
          (L : EReal) ≤ ((⨅ (l₁ : ℝ) (_ : growthRate Ψ ν p < ENNReal.ofReal l₁) (_ : l₁ < lam),
            DLower Ψ p l₁ ζ : ENNReal) : EReal)) ∧
      (∀ lam : ℝ, 0 ≤ lam → ∀ ζ : Ξ, ⊥ < Phi Ψ p lam ζ →
        ∃ R : EReal,
          Tendsto (fun l : ℝ =>
              ((((Phi Ψ p l ζ).toReal - (Phi Ψ p lam ζ).toReal) / (l - lam) : ℝ) : EReal))
            (𝓝[>] lam) (𝓝 R) ∧
          ((⨆ (l₂ : ℝ) (_ : lam < l₂), DUpper Ψ p l₂ ζ : ENNReal) : EReal) ≤ R ∧
          R ≤ ((DLower Ψ p lam ζ : ENNReal) : EReal)) := by sorry

end DRSOWass.Duality
