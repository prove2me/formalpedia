-- Prove2me | Theorems.Thm_DRSOWass_Duality_lemma_7_kappa_zero
-- name    : DRSOWass.Duality.lemma_7_kappa_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:28:02.673456+00:00
-- url     : https://prove2.me/theorems/75087a4b-8570-465d-bf28-a49e1eb1a502
-- title:
--   Lemma 7, case κ = 0 — ε-optimal primal solution when κ = 0 is the unique dual minimizer
-- statement:
--   Let $(\Xi,d)$ be a Polish space, $p\in[1,\infty)$, $\theta>0$, $\nu$ a Borel probability measure, $\Psi\in L^1(\nu)$ Borel measurable, with $\kappa<\infty$, and suppose $\kappa$ is the unique minimizer of $h$ on $[0,\infty)$. If $\kappa=0$, then for every $\varepsilon>0$ there are $\lambda^\varepsilon\in(0,\varepsilon)$ and a $\nu$-measurable $T^\varepsilon:\Xi\to\Xi$ with
--   $$\lambda^\varepsilon d^p(T^\varepsilon(\zeta),\zeta)-\Psi(T^\varepsilon(\zeta))\le\Phi(\lambda^\varepsilon,\zeta)+\varepsilon\quad\text{for }\nu\text{-a.e. }\zeta,$$
--   such that $\mu^\varepsilon=T^\varepsilon_\#\nu$ satisfies
--   $$\int_\Xi\Psi\,d\mu^\varepsilon\ge\kappa\theta^p-\int_\Xi\Phi(\kappa,\zeta)\,\nu(d\zeta)-\varepsilon\quad(17)$$
--   and
--   $$W_p^p(\mu^\varepsilon,\nu)\le\int_\Xi d^p(T^\varepsilon(\zeta),\zeta)\,\nu(d\zeta)\le\theta^p.\quad(18)$$
--
--   This is the boundary case $\lambda^*=\kappa=0$ of the strong duality proof.
--
--   **Formalization Note** "$\kappa$ is the unique minimizer of $h$" is $h(\kappa)\le h(\lambda)$ for all $\lambda\ge0$ together with: $h(\lambda)\le h(\kappa)$ and $\lambda\ge 0$ imply $\lambda=\kappa$. $\kappa$ is used as a real number through its finiteness. Integrals as in Lemma 6. Borel measurability of $\Psi$ is added, as in p. 5.
-- source:
--   Gao, Kleywegt, Distributionally Robust Stochastic Optimization with Wasserstein Distance, arXiv:1604.02199v3, p. 14, Lemma 7 (case κ = 0), (17), (18)

import Mathlib
import Definitions.Def_DRSOWass_Duality_Setting

open MeasureTheory Filter Topology

namespace DRSOWass.Duality

/-- Lemma 7 (Structure of ε-optimal primal solution with λ* = κ), case `κ = 0`, p. 14. -/
theorem lemma_7_kappa_zero {Ξ : Type*} [MetricSpace Ξ] [CompleteSpace Ξ] [SecondCountableTopology Ξ]
    [MeasurableSpace Ξ] [BorelSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (Ψ : Ξ → ℝ) (p : ℝ) (θ : ℝ)
    (hp : 1 ≤ p) (hθ : 0 < θ) (hΨm : Measurable Ψ) (hΨ : Integrable Ψ ν)
    (hκ : growthRate Ψ ν p < ⊤)
    (hmin : ∀ lam : ℝ, 0 ≤ lam →
      dualObj Ψ ν p θ (growthRate Ψ ν p).toReal ≤ dualObj Ψ ν p θ lam)
    (huniq : ∀ lam : ℝ, 0 ≤ lam →
      dualObj Ψ ν p θ lam ≤ dualObj Ψ ν p θ (growthRate Ψ ν p).toReal →
        lam = (growthRate Ψ ν p).toReal)
    (hκ0 : growthRate Ψ ν p = 0) :
    ∀ ε : ℝ, 0 < ε →
      ∃ (le : ℝ) (T : Ξ → Ξ), 0 < le ∧ le < ε ∧ AEMeasurable T ν ∧
        (∀ᵐ ζ ∂ν, ((le * dist (T ζ) ζ ^ p - Ψ (T ζ) : ℝ) : EReal) ≤ Phi Ψ p le ζ + (ε : EReal)) ∧
        (((growthRate Ψ ν p).toReal * θ ^ p : ℝ) : EReal) -
            ModelRiskOT.Duality.extIntegral ν (Phi Ψ p (growthRate Ψ ν p).toReal) - (ε : EReal) ≤
          ModelRiskOT.Duality.extIntegral (ν.map T) (fun ξ => (Ψ ξ : EReal)) ∧
        wassPow p (ν.map T) ν ≤ ∫⁻ ζ, ENNReal.ofReal (dist (T ζ) ζ ^ p) ∂ν ∧
        ∫⁻ ζ, ENNReal.ofReal (dist (T ζ) ζ ^ p) ∂ν ≤ ENNReal.ofReal (θ ^ p) := by sorry

end DRSOWass.Duality
