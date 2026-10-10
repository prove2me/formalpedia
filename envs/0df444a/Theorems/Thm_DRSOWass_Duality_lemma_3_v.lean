-- Prove2me | Theorems.Thm_DRSOWass_Duality_lemma_3_v
-- name    : DRSOWass.Duality.lemma_3_v
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:29:37.7976+00:00
-- url     : https://prove2.me/theorems/19e30a25-d1b6-4f41-ba79-f9330abd1e14
-- title:
--   Lemma 3(v) — ν-measurable selection of a far point with Ψ(ξ) − Ψ(ζ) ≥ κ′d^p(ξ,ζ)
-- statement:
--   Let $(\Xi,d)$ be a Polish space, $p\in[1,\infty)$, $\nu$ a Borel probability measure, $\Psi\in L^1(\nu)$ Borel measurable, and suppose $\kappa<\infty$. Let $\kappa'\in(0,\kappa)$ and let $M:\Xi\to\mathbb R$ be $\nu$-measurable. If the set
--   $$F(\zeta)=\{\xi\in\Xi:\ \Psi(\xi)-\Psi(\zeta)\ge\kappa' d^p(\xi,\zeta),\ d^p(\xi,\zeta)\ge M(\zeta)\}$$
--   is nonempty for $\nu$-almost every $\zeta$, then there is a $\nu$-measurable $T:\Xi\to\Xi$ with $T(\zeta)\in F(\zeta)$ for $\nu$-almost every $\zeta$.
--
--   This selection moves mass far away at a rate of increase of $\Psi$ just below the growth rate, which is how worst-case distributions are approximated when the dual minimizer is $\kappa$ itself.
--
--   **Formalization Note** $\nu$-measurability of $M$ is null-measurability, of $T$ almost-everywhere measurability. Borel measurability of $\Psi$ is added, as in p. 5.
-- source:
--   Gao, Kleywegt, Distributionally Robust Stochastic Optimization with Wasserstein Distance, arXiv:1604.02199v3, pp. 9–10, Lemma 3(v)

import Mathlib
import Definitions.Def_DRSOWass_Duality_Setting

open MeasureTheory Filter Topology

namespace DRSOWass.Duality

/-- Lemma 3(v), p. 10: if `κ < ∞`, `κ' ∈ (0, κ)` and `M` is `ν`-measurable such that
`F(ζ) = {ξ : Ψ(ξ) − Ψ(ζ) ≥ κ' d^p(ξ, ζ), d^p(ξ, ζ) ≥ M(ζ)}` is nonempty for `ν`-a.e. `ζ`,
there is a `ν`-measurable `T` with `T(ζ) ∈ F(ζ)` for `ν`-a.e. `ζ`. -/
theorem lemma_3_v {Ξ : Type*} [MetricSpace Ξ] [CompleteSpace Ξ] [SecondCountableTopology Ξ]
    [MeasurableSpace Ξ] [BorelSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (Ψ : Ξ → ℝ) (p : ℝ)
    (hp : 1 ≤ p) (hΨm : Measurable Ψ) (hΨ : Integrable Ψ ν)
    (hκ : growthRate Ψ ν p < ⊤)
    (κ' : ℝ) (hκ'0 : 0 < κ') (hκ' : ENNReal.ofReal κ' < growthRate Ψ ν p)
    (M : Ξ → ℝ) (hM : NullMeasurable M ν)
    (hF : ∀ᵐ ζ ∂ν, {ξ : Ξ | κ' * dist ξ ζ ^ p ≤ Ψ ξ - Ψ ζ ∧ M ζ ≤ dist ξ ζ ^ p}.Nonempty) :
    ∃ T : Ξ → Ξ, AEMeasurable T ν ∧
      ∀ᵐ ζ ∂ν, κ' * dist (T ζ) ζ ^ p ≤ Ψ (T ζ) - Ψ ζ ∧ M ζ ≤ dist (T ζ) ζ ^ p := by sorry

end DRSOWass.Duality
