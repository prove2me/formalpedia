-- Prove2me | Theorems.Thm_DRSOWass_Duality_lemma_7_kappa_pos
-- name    : DRSOWass.Duality.lemma_7_kappa_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:28:31.920066+00:00
-- url     : https://prove2.me/theorems/bee7f9d5-261e-4030-9a58-715e3543c0ca
-- title:
--   Lemma 7, case κ > 0 — ε-optimal primal solution when κ > 0 is the unique dual minimizer
-- statement:
--   Let $(\Xi,d)$ be a Polish space, $p\in[1,\infty)$, $\theta>0$, $\nu$ a Borel probability measure, $\Psi\in L^1(\nu)$ Borel measurable, with $\kappa<\infty$, and suppose $\kappa$ is the unique minimizer of $h$ on $[0,\infty)$. If $\kappa>0$, then for every $\varepsilon>0$ there are $\lambda_1^\varepsilon\in(\kappa-\varepsilon,\kappa)$, $\lambda_2^\varepsilon\in(\kappa,\kappa+\varepsilon)$, $\nu$-measurable maps $T_1^\varepsilon,T_2^\varepsilon:\Xi\to\Xi$ and $p^\varepsilon\in(0,1)$ such that, for $\nu$-almost every $\zeta$,
--   $$\Psi(T_1^\varepsilon(\zeta))-\Psi(\zeta)\ge\lambda_1^\varepsilon d^p(T_1^\varepsilon(\zeta),\zeta),\qquad \lambda_2^\varepsilon d^p(T_2^\varepsilon(\zeta),\zeta)-\Psi(T_2^\varepsilon(\zeta))\le\Phi(\lambda_2^\varepsilon,\zeta)+\varepsilon,$$
--   $\int_\Xi d^p(T_1^\varepsilon(\zeta),\zeta)\,\nu(d\zeta)>\theta^p+\theta^p/\varepsilon$, and $\mu^\varepsilon=p^\varepsilon T^\varepsilon_{1\#}\nu+(1-p^\varepsilon)T^\varepsilon_{2\#}\nu$ satisfies (17),
--   $$\int_\Xi\Psi\,d\mu^\varepsilon\ge\kappa\theta^p-\int_\Xi\Phi(\kappa,\zeta)\,\nu(d\zeta)-\varepsilon,$$
--   and
--   $$W_p^p(\mu^\varepsilon,\nu)\le p^\varepsilon\int_\Xi d^p(T_1^\varepsilon(\zeta),\zeta)\,\nu(d\zeta)+(1-p^\varepsilon)\int_\Xi d^p(T_2^\varepsilon(\zeta),\zeta)\,\nu(d\zeta)=\theta^p.\quad(19)$$
--
--   Here a small fraction of mass is sent very far at a rate of increase just below $\kappa$; this is the case where no worst-case distribution need exist.
--
--   **Formalization Note** Uniqueness of the minimizer as in the case $\kappa=0$; $\kappa$ is used as a real number through its finiteness. Integrals as in Lemma 6. Borel measurability of $\Psi$ is added, as in p. 5.
-- source:
--   Gao, Kleywegt, Distributionally Robust Stochastic Optimization with Wasserstein Distance, arXiv:1604.02199v3, p. 14, Lemma 7 (case κ > 0), (17), (19)

import Mathlib
import Definitions.Def_DRSOWass_Duality_Setting

open MeasureTheory Filter Topology

namespace DRSOWass.Duality

/-- Lemma 7 (Structure of ε-optimal primal solution with λ* = κ), case `κ > 0`, p. 14. -/
theorem lemma_7_kappa_pos {Ξ : Type*} [MetricSpace Ξ] [CompleteSpace Ξ] [SecondCountableTopology Ξ]
    [MeasurableSpace Ξ] [BorelSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (Ψ : Ξ → ℝ) (p : ℝ) (θ : ℝ)
    (hp : 1 ≤ p) (hθ : 0 < θ) (hΨm : Measurable Ψ) (hΨ : Integrable Ψ ν)
    (hκ : growthRate Ψ ν p < ⊤)
    (hmin : ∀ lam : ℝ, 0 ≤ lam →
      dualObj Ψ ν p θ (growthRate Ψ ν p).toReal ≤ dualObj Ψ ν p θ lam)
    (huniq : ∀ lam : ℝ, 0 ≤ lam →
      dualObj Ψ ν p θ lam ≤ dualObj Ψ ν p θ (growthRate Ψ ν p).toReal →
        lam = (growthRate Ψ ν p).toReal)
    (hκpos : 0 < growthRate Ψ ν p) :
    ∀ ε : ℝ, 0 < ε →
      ∃ (l₁ l₂ : ℝ) (T₁ T₂ : Ξ → Ξ) (q : ℝ),
        (growthRate Ψ ν p).toReal - ε < l₁ ∧ l₁ < (growthRate Ψ ν p).toReal ∧
        (growthRate Ψ ν p).toReal < l₂ ∧ l₂ < (growthRate Ψ ν p).toReal + ε ∧
        AEMeasurable T₁ ν ∧ AEMeasurable T₂ ν ∧ 0 < q ∧ q < 1 ∧
        (∀ᵐ ζ ∂ν, l₁ * dist (T₁ ζ) ζ ^ p ≤ Ψ (T₁ ζ) - Ψ ζ ∧
          ((l₂ * dist (T₂ ζ) ζ ^ p - Ψ (T₂ ζ) : ℝ) : EReal) ≤ Phi Ψ p l₂ ζ + (ε : EReal)) ∧
        ENNReal.ofReal (θ ^ p + θ ^ p / ε) < ∫⁻ ζ, ENNReal.ofReal (dist (T₁ ζ) ζ ^ p) ∂ν ∧
        (((growthRate Ψ ν p).toReal * θ ^ p : ℝ) : EReal) -
            ModelRiskOT.Duality.extIntegral ν (Phi Ψ p (growthRate Ψ ν p).toReal) - (ε : EReal) ≤
          ModelRiskOT.Duality.extIntegral
            (ENNReal.ofReal q • ν.map T₁ + ENNReal.ofReal (1 - q) • ν.map T₂)
            (fun ξ => (Ψ ξ : EReal)) ∧
        wassPow p (ENNReal.ofReal q • ν.map T₁ + ENNReal.ofReal (1 - q) • ν.map T₂) ν ≤
          ENNReal.ofReal q * ∫⁻ ζ, ENNReal.ofReal (dist (T₁ ζ) ζ ^ p) ∂ν +
            ENNReal.ofReal (1 - q) * ∫⁻ ζ, ENNReal.ofReal (dist (T₂ ζ) ζ ^ p) ∂ν ∧
        ENNReal.ofReal q * ∫⁻ ζ, ENNReal.ofReal (dist (T₁ ζ) ζ ^ p) ∂ν +
            ENNReal.ofReal (1 - q) * ∫⁻ ζ, ENNReal.ofReal (dist (T₂ ζ) ζ ^ p) ∂ν =
          ENNReal.ofReal (θ ^ p) := by sorry

end DRSOWass.Duality
