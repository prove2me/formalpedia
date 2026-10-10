-- Prove2me | Theorems.Thm_DRSOWass_Duality_proposition_1
-- name    : DRSOWass.Duality.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:28:16.694526+00:00
-- url     : https://prove2.me/theorems/e4844237-e402-4bd4-9dc1-63aee792a565
-- title:
--   Proposition 1 — weak duality v_P ≤ v_D
-- statement:
--   Let $(\Xi,d)$ be a Polish space, $\nu$ a Borel probability measure on $\Xi$, $\Psi\in L^1(\nu)$ a Borel measurable function, $p\in[1,\infty)$ and $\theta>0$. Let $v_P$ be the worst-case expectation of $\Psi$ over the Wasserstein ball $\{\mu\in\mathcal P(\Xi):W_p(\mu,\nu)\le\theta\}$ and $v_D=\inf_{\lambda\ge0}\{\lambda\theta^p-\int_\Xi\Phi(\lambda,\zeta)\,\nu(d\zeta)\}$ the one-dimensional dual, with $\Phi(\lambda,\zeta)=\inf_{\xi}\{\lambda d^p(\xi,\zeta)-\Psi(\xi)\}$. Then
--   $$v_P\le v_D.$$
--
--   Weak duality is the easy half of the strong duality theorem; it holds without any growth condition on $\Psi$.
--
--   **Formalization Note** "$\Psi\in L^1(\nu)$" only makes $\Psi$ measurable for the $\nu$-completion; the statement adds Borel measurability of $\Psi$ (the paper's p. 5 speaks of a "measurable function $\Psi$"), without which $\int\Psi\,d\mu$ is not defined for $\mu\ne\nu$. Integrals are extended-real ($\int\Psi^+-\int\Psi^-$), so $v_P,v_D\in[-\infty,\infty]$.
-- source:
--   Gao, Kleywegt, Distributionally Robust Stochastic Optimization with Wasserstein Distance, arXiv:1604.02199v3, p. 8, Proposition 1

import Mathlib
import Definitions.Def_DRSOWass_Duality_Setting

open MeasureTheory Filter Topology

namespace DRSOWass.Duality

/-- Proposition 1 (Weak duality), p. 8: for `ν ∈ P(Ξ)`, `Ψ ∈ L¹(ν)` (Borel measurable),
`p ∈ [1, ∞)` and `θ > 0`, `v_P ≤ v_D`. -/
theorem proposition_1 {Ξ : Type*} [MetricSpace Ξ] [CompleteSpace Ξ] [SecondCountableTopology Ξ]
    [MeasurableSpace Ξ] [BorelSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (Ψ : Ξ → ℝ) (p : ℝ) (θ : ℝ)
    (hp : 1 ≤ p) (hθ : 0 < θ) (hΨm : Measurable Ψ) (hΨ : Integrable Ψ ν) :
    vP Ψ ν p θ ≤ vD Ψ ν p θ := by sorry

end DRSOWass.Duality
