-- Prove2me | Theorems.Thm_DRSOWass_Duality_lemma_5_v
-- name    : DRSOWass.Duality.lemma_5_v
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:28:02.185289+00:00
-- url     : https://prove2.me/theorems/1f1051a7-6e7e-4679-aa0d-bda5c99afed0
-- title:
--   Lemma 5(v) — h has a minimizer λ* ∈ [κ, ∞)
-- statement:
--   Let $(\Xi,d)$ be a Polish space, $p\in[1,\infty)$, $\theta>0$, $\nu$ a Borel probability measure, $\Psi\in L^1(\nu)$ Borel measurable, and suppose the growth rate is finite, $\kappa<\infty$. Then the dual objective $h(\lambda)=\lambda\theta^p-\int_\Xi\Phi(\lambda,\zeta)\,\nu(d\zeta)$ attains its infimum over $[0,\infty)$ at some
--   $$\lambda^*\in[\kappa,\infty).$$
--
--   The existence of a dual minimizer is the starting point of the strong duality proof, which then distinguishes $\lambda^*>\kappa$ from $\lambda^*=\kappa$.
--
--   **Formalization Note** The hypothesis $\kappa<\infty$ is not printed in Lemma 5 but is needed for $[\kappa,\infty)$ to be nonempty; it is the standing hypothesis of the surrounding Lemmas 4, 6, 7. Borel measurability of $\Psi$ is added, as in p. 5.
-- source:
--   Gao, Kleywegt, Distributionally Robust Stochastic Optimization with Wasserstein Distance, arXiv:1604.02199v3, p. 11, Lemma 5(v)

import Mathlib
import Definitions.Def_DRSOWass_Duality_Setting

open MeasureTheory Filter Topology

namespace DRSOWass.Duality

/-- Lemma 5(v), p. 11: if `κ < ∞` and `θ > 0`, then `h` has a minimizer `λ* ∈ [κ, ∞)` over
`[0, ∞)`. -/
theorem lemma_5_v {Ξ : Type*} [MetricSpace Ξ] [CompleteSpace Ξ] [SecondCountableTopology Ξ]
    [MeasurableSpace Ξ] [BorelSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (Ψ : Ξ → ℝ) (p : ℝ) (θ : ℝ)
    (hp : 1 ≤ p) (hθ : 0 < θ) (hΨm : Measurable Ψ) (hΨ : Integrable Ψ ν)
    (hκ : growthRate Ψ ν p < ⊤) :
    ∃ ls : ℝ, 0 ≤ ls ∧ growthRate Ψ ν p ≤ ENNReal.ofReal ls ∧
      ∀ lam : ℝ, 0 ≤ lam → dualObj Ψ ν p θ ls ≤ dualObj Ψ ν p θ lam := by sorry

end DRSOWass.Duality
