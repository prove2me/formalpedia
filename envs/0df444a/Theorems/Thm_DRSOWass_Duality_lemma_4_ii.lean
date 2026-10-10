-- Prove2me | Theorems.Thm_DRSOWass_Duality_lemma_4_ii
-- name    : DRSOWass.Duality.lemma_4_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:28:30.432257+00:00
-- url     : https://prove2.me/theorems/02eb2065-2a8b-4408-a703-702f1f8a8aea
-- title:
--   Lemma 4(ii) — (λ₂ − λ₁)D̄(λ₂,ζ) ≤ −Ψ(ζ) − Φ(λ₁,ζ)
-- statement:
--   Let $(\Xi,d)$ be a Polish space, $p\in[1,\infty)$, $\nu$ a Borel probability measure, $\Psi\in L^1(\nu)$ Borel measurable, with $\kappa<\infty$. For every $\zeta\in\Xi$ and all $\lambda_2>\lambda_1$ with $\Phi(\lambda_1,\zeta)>-\infty$,
--   $$(\lambda_2-\lambda_1)\,\overline D(\lambda_2,\zeta)\le-\Psi(\zeta)-\Phi(\lambda_1,\zeta).$$
--
--   In particular $\overline D(\lambda_2,\zeta)$ is finite as soon as $\Phi(\lambda_1,\zeta)$ is finite for some smaller $\lambda_1$, so near-optimal transport distances stay bounded above the growth rate.
--
--   **Formalization Note** The inequality is in the extended reals; both sides are nonnegative and the right-hand side is finite under the hypothesis. The point $\zeta$, free in the printed statement, is universally quantified. Borel measurability of $\Psi$ is added, as in p. 5.
-- source:
--   Gao, Kleywegt, Distributionally Robust Stochastic Optimization with Wasserstein Distance, arXiv:1604.02199v3, pp. 10–11, Lemma 4(ii)

import Mathlib
import Definitions.Def_DRSOWass_Duality_Setting

open MeasureTheory Filter Topology

namespace DRSOWass.Duality

/-- Lemma 4(ii) (Bounds), p. 11, for `κ < ∞`: for `λ₁ < λ₂` and `ζ` with
`Φ(λ₁, ζ) > −∞`, `(λ₂ − λ₁) D̄(λ₂, ζ) ≤ −Ψ(ζ) − Φ(λ₁, ζ)`. -/
theorem lemma_4_ii {Ξ : Type*} [MetricSpace Ξ] [CompleteSpace Ξ] [SecondCountableTopology Ξ]
    [MeasurableSpace Ξ] [BorelSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (Ψ : Ξ → ℝ) (p : ℝ)
    (hp : 1 ≤ p) (hΨm : Measurable Ψ) (hΨ : Integrable Ψ ν)
    (hκ : growthRate Ψ ν p < ⊤) :
    ∀ l₁ l₂ : ℝ, l₁ < l₂ → ∀ ζ : Ξ, ⊥ < Phi Ψ p l₁ ζ →
      ((l₂ - l₁ : ℝ) : EReal) * ((DUpper Ψ p l₂ ζ : ENNReal) : EReal) ≤
        -((Ψ ζ : ℝ) : EReal) - Phi Ψ p l₁ ζ := by sorry

end DRSOWass.Duality
