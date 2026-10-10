-- Prove2me | Theorems.Thm_DRSOWass_Duality_lemma_5_i_iv
-- name    : DRSOWass.Duality.lemma_5_i_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:28:49.351311+00:00
-- url     : https://prove2.me/theorems/af14632d-da9a-45cb-86f2-2479e34af84d
-- title:
--   Lemma 5(i)–(iv) — the dual objective h is ∞ below κ, finite above κ, convex, lower semicontinuous and coercive
-- statement:
--   Let $(\Xi,d)$ be a Polish space, $p\in[1,\infty)$, $\theta>0$, $\nu$ a Borel probability measure and $\Psi\in L^1(\nu)$ Borel measurable. Let
--   $$h(\lambda)=\lambda\theta^p-\int_\Xi\Phi(\lambda,\zeta)\,\nu(d\zeta),\qquad\lambda\ge0,$$
--   be the dual objective function. Then:
--
--   1. $h(\lambda)=\infty$ for all $\lambda\in[0,\kappa)$ and $h(\lambda)<\infty$ for all $\lambda\in(\kappa,\infty)$;
--   2. $h$ is convex on $[0,\infty)$;
--   3. $h$ is lower semicontinuous on $[0,\infty)$;
--   4. $h(\lambda)\to\infty$ as $\lambda\to\infty$.
--
--   These properties reduce the dual problem to a well-behaved one-dimensional convex minimization whose effective domain starts at the growth rate.
--
--   **Formalization Note** $h$ takes values in $(-\infty,\infty]$ (since $-\Phi(\lambda,\zeta)\ge\Psi(\zeta)$ and $\Psi\in L^1(\nu)$), so convexity is the explicit inequality $h(t\lambda_1+(1-t)\lambda_2)\le t h(\lambda_1)+(1-t)h(\lambda_2)$ in the extended reals, with $t\cdot\infty=\infty$ for $t>0$. The lemma is printed without a hypothesis on $\kappa$ and is stated so (when $\kappa=\infty$, $h\equiv\infty$ on $[0,\infty)$ and all four items still hold). Borel measurability of $\Psi$ is added, as in p. 5.
-- source:
--   Gao, Kleywegt, Distributionally Robust Stochastic Optimization with Wasserstein Distance, arXiv:1604.02199v3, p. 11, Lemma 5(i)–(iv)

import Mathlib
import Definitions.Def_DRSOWass_Duality_Setting

open MeasureTheory Filter Topology

namespace DRSOWass.Duality

/-- Lemma 5(i)–(iv) (Dual objective function), p. 11: for `θ > 0`,
(i) `h(λ) = ∞` for `λ ∈ [0, κ)` and `h(λ) < ∞` for `λ ∈ (κ, ∞)`;
(ii) `h` is convex on `[0, ∞)`; (iii) `h` is lower semicontinuous on `[0, ∞)`;
(iv) `h(λ) → ∞` as `λ → ∞`. -/
theorem lemma_5_i_iv {Ξ : Type*} [MetricSpace Ξ] [CompleteSpace Ξ] [SecondCountableTopology Ξ]
    [MeasurableSpace Ξ] [BorelSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (Ψ : Ξ → ℝ) (p : ℝ) (θ : ℝ)
    (hp : 1 ≤ p) (hθ : 0 < θ) (hΨm : Measurable Ψ) (hΨ : Integrable Ψ ν) :
    (∀ lam : ℝ, 0 ≤ lam → ENNReal.ofReal lam < growthRate Ψ ν p → dualObj Ψ ν p θ lam = ⊤) ∧
    (∀ lam : ℝ, growthRate Ψ ν p < ENNReal.ofReal lam → dualObj Ψ ν p θ lam < ⊤) ∧
    (∀ l₁ l₂ : ℝ, 0 ≤ l₁ → 0 ≤ l₂ → ∀ t : ℝ, 0 < t → t < 1 →
      dualObj Ψ ν p θ (t * l₁ + (1 - t) * l₂) ≤
        ((t : ℝ) : EReal) * dualObj Ψ ν p θ l₁ + ((1 - t : ℝ) : EReal) * dualObj Ψ ν p θ l₂) ∧
    LowerSemicontinuousOn (dualObj Ψ ν p θ) (Set.Ici 0) ∧
    Tendsto (dualObj Ψ ν p θ) atTop (𝓝 ⊤) := by sorry

end DRSOWass.Duality
