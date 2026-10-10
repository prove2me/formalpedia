-- Prove2me | Theorems.Thm_DRSOWass_Duality_lemma_3_ii
-- name    : DRSOWass.Duality.lemma_3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:28:57.400803+00:00
-- url     : https://prove2.me/theorems/ea784956-2623-4a41-a0c8-99603fdc3a0c
-- title:
--   Lemma 3(ii) — ν-measurable selections of the near-optimal sets F̄^ε_δ and F̲^ε_δ
-- statement:
--   Let $(\Xi,d)$ be a Polish space, $p\in[1,\infty)$, $\nu$ a Borel probability measure, $\Psi\in L^1(\nu)$ Borel measurable, and suppose the growth rate satisfies $\kappa<\infty$. Let $\lambda,\delta,\varepsilon\ge 0$ and
--   $$\overline F^\varepsilon_\delta(\lambda,\zeta)=\{\xi:\lambda d^p(\xi,\zeta)-\Psi(\xi)\le\Phi(\lambda,\zeta)+\varepsilon,\ d^p(\xi,\zeta)\ge\overline D(\lambda,\zeta)-\delta\},$$
--   $$\underline F^\varepsilon_\delta(\lambda,\zeta)=\{\xi:\lambda d^p(\xi,\zeta)-\Psi(\xi)\le\Phi(\lambda,\zeta)+\varepsilon,\ d^p(\xi,\zeta)\le\underline D(\lambda,\zeta)+\delta\}.$$
--   If both sets are nonempty for $\nu$-almost every $\zeta$, then there are $\nu$-measurable maps $\overline T,\underline T:\Xi\to\Xi$ with $\overline T(\zeta)\in\overline F^\varepsilon_\delta(\lambda,\zeta)$ and $\underline T(\zeta)\in\underline F^\varepsilon_\delta(\lambda,\zeta)$ for $\nu$-almost every $\zeta$.
--
--   These selections are the transport maps out of which near-optimal worst-case distributions are built.
--
--   **Formalization Note** $\nu$-measurable maps are `AEMeasurable` maps (equivalent for a Polish target). $\overline D$ is $[0,\infty]$-valued and $\overline D-\delta$ is truncated at $0$, which does not change the set since $d^p\ge 0$. Borel measurability of $\Psi$ is added, as in p. 5.
-- source:
--   Gao, Kleywegt, Distributionally Robust Stochastic Optimization with Wasserstein Distance, arXiv:1604.02199v3, pp. 9–10, Lemma 3(ii)

import Mathlib
import Definitions.Def_DRSOWass_Duality_Setting

open MeasureTheory Filter Topology

namespace DRSOWass.Duality

/-- Lemma 3(ii), p. 10: if `κ < ∞`, then for `λ, δ, ε ≥ 0` such that `F̄^ε_δ(λ, ζ)` and
`F̲^ε_δ(λ, ζ)` are nonempty for `ν`-a.e. `ζ`, there are `ν`-measurable selections of both. -/
theorem lemma_3_ii {Ξ : Type*} [MetricSpace Ξ] [CompleteSpace Ξ] [SecondCountableTopology Ξ]
    [MeasurableSpace Ξ] [BorelSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (Ψ : Ξ → ℝ) (p : ℝ)
    (hp : 1 ≤ p) (hΨm : Measurable Ψ) (hΨ : Integrable Ψ ν)
    (hκ : growthRate Ψ ν p < ⊤)
    (lam δ ε : ℝ) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hU : ∀ᵐ ζ ∂ν, (FUpper Ψ p lam δ ε ζ).Nonempty)
    (hL : ∀ᵐ ζ ∂ν, (FLower Ψ p lam δ ε ζ).Nonempty) :
    (∃ T : Ξ → Ξ, AEMeasurable T ν ∧ ∀ᵐ ζ ∂ν, T ζ ∈ FUpper Ψ p lam δ ε ζ) ∧
    (∃ T : Ξ → Ξ, AEMeasurable T ν ∧ ∀ᵐ ζ ∂ν, T ζ ∈ FLower Ψ p lam δ ε ζ) := by sorry

end DRSOWass.Duality
