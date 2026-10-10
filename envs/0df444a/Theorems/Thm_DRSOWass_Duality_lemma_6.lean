-- Prove2me | Theorems.Thm_DRSOWass_Duality_lemma_6
-- name    : DRSOWass.Duality.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:28:11.384998+00:00
-- url     : https://prove2.me/theorems/faf6fa32-ad48-47af-b375-0efa149617b2
-- title:
--   Lemma 6 — ε-optimal primal solution when h has a minimizer λ* > κ
-- statement:
--   Let $(\Xi,d)$ be a Polish space, $p\in[1,\infty)$, $\theta>0$, $\nu$ a Borel probability measure, $\Psi\in L^1(\nu)$ Borel measurable, with $\kappa<\infty$. Suppose $h$ has a minimizer $\lambda^*>\kappa$ on $[0,\infty)$. Then for every $\varepsilon>0$ there are $\lambda_1^\varepsilon\in(\max\{\kappa,\lambda^*-\varepsilon\},\lambda^*)$, $\lambda_2^\varepsilon\in(\lambda^*,\lambda^*+\varepsilon)$, $\delta^\varepsilon\in(0,\varepsilon)$, $\nu$-measurable maps $T_1^\varepsilon,T_2^\varepsilon:\Xi\to\Xi$ and weights $p_1^\varepsilon,p_2^\varepsilon,p_3^\varepsilon\ge0$ summing to $1$, such that for $\nu$-almost every $\zeta$
--   $$T_1^\varepsilon(\zeta)\in\overline F^{\varepsilon}_{\delta^\varepsilon}(\lambda_1^\varepsilon,\zeta),\qquad T_2^\varepsilon(\zeta)\in\underline F^{\varepsilon}_{\delta^\varepsilon}(\lambda_2^\varepsilon,\zeta),$$
--   and the mixture $\mu^\varepsilon=p_1^\varepsilon T^\varepsilon_{1\#}\nu+p_2^\varepsilon T^\varepsilon_{2\#}\nu+p_3^\varepsilon\nu$ satisfies
--   $$\int_\Xi\Psi\,d\mu^\varepsilon\ge\lambda^*\theta^p-\int_\Xi\Phi(\lambda^*,\zeta)\,\nu(d\zeta)-\varepsilon$$
--   and
--   $$W_p^p(\mu^\varepsilon,\nu)\le p_1^\varepsilon\int_\Xi d^p(T_1^\varepsilon(\zeta),\zeta)\,\nu(d\zeta)+p_2^\varepsilon\int_\Xi d^p(T_2^\varepsilon(\zeta),\zeta)\,\nu(d\zeta)\le\theta^p.$$
--
--   So $\mu^\varepsilon$ lies in the Wasserstein ball and is $\varepsilon$-optimal for the dual value; this is one of the two cases of the strong duality proof.
--
--   **Formalization Note** The printed (7) writes the weights as $p_1,p_2$; they are $p_1^\varepsilon,p_2^\varepsilon$, the only weights in scope. $\overline F$, $\underline F$ are the sets of Lemma 3(ii). Push-forwards use `AEMeasurable` maps; $\int\Psi\,d\mu^\varepsilon$ is the extended-real integral and the transport integrals are lower Lebesgue integrals in $[0,\infty]$. Borel measurability of $\Psi$ is added, as in p. 5.
-- source:
--   Gao, Kleywegt, Distributionally Robust Stochastic Optimization with Wasserstein Distance, arXiv:1604.02199v3, p. 11, Lemma 6, (6), (7)

import Mathlib
import Definitions.Def_DRSOWass_Duality_Setting

open MeasureTheory Filter Topology

namespace DRSOWass.Duality

/-- Lemma 6 (Structure of ε-optimal primal solution with λ* > κ), p. 11. -/
theorem lemma_6 {Ξ : Type*} [MetricSpace Ξ] [CompleteSpace Ξ] [SecondCountableTopology Ξ]
    [MeasurableSpace Ξ] [BorelSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (Ψ : Ξ → ℝ) (p : ℝ) (θ : ℝ)
    (hp : 1 ≤ p) (hθ : 0 < θ) (hΨm : Measurable Ψ) (hΨ : Integrable Ψ ν)
    (hκ : growthRate Ψ ν p < ⊤)
    (ls : ℝ) (hls0 : 0 ≤ ls) (hlsκ : growthRate Ψ ν p < ENNReal.ofReal ls)
    (hmin : ∀ lam : ℝ, 0 ≤ lam → dualObj Ψ ν p θ ls ≤ dualObj Ψ ν p θ lam) :
    ∀ ε : ℝ, 0 < ε →
      ∃ (l₁ l₂ δ : ℝ) (T₁ T₂ : Ξ → Ξ) (q₁ q₂ q₃ : ℝ),
        growthRate Ψ ν p < ENNReal.ofReal l₁ ∧ ls - ε < l₁ ∧ l₁ < ls ∧
        ls < l₂ ∧ l₂ < ls + ε ∧ 0 < δ ∧ δ < ε ∧
        AEMeasurable T₁ ν ∧ AEMeasurable T₂ ν ∧
        0 ≤ q₁ ∧ 0 ≤ q₂ ∧ 0 ≤ q₃ ∧ q₁ + q₂ + q₃ = 1 ∧
        (∀ᵐ ζ ∂ν, T₁ ζ ∈ FUpper Ψ p l₁ δ ε ζ ∧ T₂ ζ ∈ FLower Ψ p l₂ δ ε ζ) ∧
        ((ls * θ ^ p : ℝ) : EReal) - ModelRiskOT.Duality.extIntegral ν (Phi Ψ p ls) - (ε : EReal) ≤
          ModelRiskOT.Duality.extIntegral
            (ENNReal.ofReal q₁ • ν.map T₁ + ENNReal.ofReal q₂ • ν.map T₂ + ENNReal.ofReal q₃ • ν)
            (fun ξ => (Ψ ξ : EReal)) ∧
        wassPow p (ENNReal.ofReal q₁ • ν.map T₁ + ENNReal.ofReal q₂ • ν.map T₂ +
            ENNReal.ofReal q₃ • ν) ν ≤
          ENNReal.ofReal q₁ * ∫⁻ ζ, ENNReal.ofReal (dist (T₁ ζ) ζ ^ p) ∂ν +
            ENNReal.ofReal q₂ * ∫⁻ ζ, ENNReal.ofReal (dist (T₂ ζ) ζ ^ p) ∂ν ∧
        ENNReal.ofReal q₁ * ∫⁻ ζ, ENNReal.ofReal (dist (T₁ ζ) ζ ^ p) ∂ν +
            ENNReal.ofReal q₂ * ∫⁻ ζ, ENNReal.ofReal (dist (T₂ ζ) ζ ^ p) ∂ν ≤
          ENNReal.ofReal (θ ^ p) := by sorry

end DRSOWass.Duality
