-- Prove2me | Theorems.Thm_DRSOWass_Duality_theorem_1
-- name    : DRSOWass.Duality.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:28:02.653326+00:00
-- url     : https://prove2.me/theorems/f9884467-1861-45a5-8460-648f5eee4b21
-- title:
--   Theorem 1 — strong duality v_P = v_D < ∞ when the growth rate κ is finite
-- statement:
--   Let $(\Xi,d)$ be a Polish space, $p\in[1,\infty)$, $\nu$ a Borel probability measure on $\Xi$, $\theta>0$, and $\Psi\in L^1(\nu)$ Borel measurable, with finite growth rate
--   $$\kappa=\inf\Big\{\lambda\ge0:\int_\Xi\Phi(\lambda,\zeta)\,\nu(d\zeta)>-\infty\Big\}<\infty,\qquad\Phi(\lambda,\zeta)=\inf_{\xi\in\Xi}\{\lambda d^p(\xi,\zeta)-\Psi(\xi)\}.$$
--   Then the worst-case expectation over the Wasserstein ball equals its one-dimensional dual and is finite:
--   $$\sup_{\mu\in\mathcal P(\Xi)}\Big\{\int_\Xi\Psi\,d\mu:W_p(\mu,\nu)\le\theta\Big\}=\inf_{\lambda\ge0}\Big\{\lambda\theta^p-\int_\Xi\Phi(\lambda,\zeta)\,\nu(d\zeta)\Big\}<\infty.$$
--
--   This turns the infinite-dimensional inner problem of Wasserstein distributionally robust stochastic optimization into a minimization over a single scalar, for an arbitrary Polish space and nominal distribution and a merely measurable integrand.
--
--   **Formalization Note** The constraint $W_p(\mu,\nu)\le\theta$ is written $W_p^p(\mu,\nu)\le\theta^p$ with $W_p^p$ the published optimal transport cost with cost $d^p$. Integrals are extended-real ($\int\varphi^+-\int\varphi^-$), not Bochner integrals, so a measure under which $\Psi$ is not integrable cannot contribute a spurious $0$. $\kappa$ is $[0,\infty]$-valued with $\kappa=\infty$ when no $\lambda$ qualifies. Borel measurability of $\Psi$ is added; the paper's p. 5 states the result for a "measurable function $\Psi$", and $\int\Psi\,d\mu$ for $\mu\ne\nu$ needs it.
-- source:
--   Gao, Kleywegt, Distributionally Robust Stochastic Optimization with Wasserstein Distance, arXiv:1604.02199v3, p. 17, Theorem 1

import Mathlib
import Definitions.Def_DRSOWass_Duality_Setting

open MeasureTheory Filter Topology

namespace DRSOWass.Duality

/-- Theorem 1 (Strong duality with finite optimal value), p. 17: for `p ∈ [1, ∞)`,
`ν ∈ P(Ξ)`, `θ > 0` and `Ψ ∈ L¹(ν)` (Borel measurable) with `κ < ∞`, `v_P = v_D < ∞`. -/
theorem theorem_1 {Ξ : Type*} [MetricSpace Ξ] [CompleteSpace Ξ] [SecondCountableTopology Ξ]
    [MeasurableSpace Ξ] [BorelSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (Ψ : Ξ → ℝ) (p : ℝ) (θ : ℝ)
    (hp : 1 ≤ p) (hθ : 0 < θ) (hΨm : Measurable Ψ) (hΨ : Integrable Ψ ν)
    (hκ : growthRate Ψ ν p < ⊤) :
    vP Ψ ν p θ = vD Ψ ν p θ ∧ vD Ψ ν p θ < ⊤ := by sorry

end DRSOWass.Duality
