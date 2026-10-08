-- Prove2me | Theorems.Thm_AdamDyn_ConstStep_lemma_8_2
-- name    : AdamDyn.ConstStep.lemma_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:15:05.320496+00:00
-- url     : https://prove2.me/theorems/d1c22a3d-f877-4d12-bd9b-0abd838b91ea
-- title:
--   Lemma 8.2 — the truncated increments $\gamma^{-1}(z^{\gamma,R}_{n+1}-z^{\gamma,R}_n)$ are uniformly integrable
-- statement:
--   Assume Assumptions 2.2, 2.5, 4.1 and Assumption 4.2 ii) with $p=2$, let $\varepsilon>0$ and fix the initial point $x_0\in\mathbb R^d$. Then there is $\bar\gamma_0>0$ such that for every $R>0$ the family of random variables
--
--   $$
--   \Big(\gamma^{-1}\big(z^{\gamma,R}_{n+1}-z^{\gamma,R}_n\big) \;:\; n\in\mathbb N,\ \gamma\in(0,\bar\gamma_0]\Big)
--   $$
--
--   is uniformly integrable, i.e. $\lim_{A\to+\infty}\sup_{n,\gamma}\mathbb E\big(\|X_{n,\gamma}\|\mathbb 1_{\|X_{n,\gamma}\|>A}\big)=0$. Here $z^{\gamma,R}=B_R(z^\gamma)$ is the constant-step Adam sequence stopped when the debiased iterate first leaves the ball of radius $R$.
--
--   Uniform integrability of the increments is what makes the family of interpolated truncated processes tight (Lemma 8.3).
--
--   **Formalization Note** "Assumption 4.2" is read as 4.2 ii) with $p=2$, as in Lemma 8.1. Expectations are lower Lebesgue integrals and $\|\cdot\|$ is the Euclidean norm of $\mathbb R^{3d}$. The index set is $\mathbb N\times(0,\bar\gamma_0]$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 22, Lemma 8.2

import Mathlib
import Definitions.Def_AdamDyn_ConstStep_StochasticModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace AdamDyn.ConstStep

/-- Lemma 8.2 (p. 22): there is `γ̄0 > 0` such that for every `R > 0` the family
`(γ⁻¹(z^{γ,R}_{n+1} − z^{γ,R}_n) : n ∈ ℕ, γ ∈ (0, γ̄0])` is uniformly integrable.
Assumption 4.2 is read as 4.2 ii) with `p = 2`. -/
theorem lemma_8_2 {d : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (gf : E d → Ξ → E d) (ξ : ℕ → Ω → Ξ)
    (αbar βbar : ℝ → ℝ) (a b ε : ℝ) (x0 : E d)
    (h22 : Assumption22 μ f gf)
    (h25 : Assumption25 αbar βbar a b)
    (h42 : Assumption42ii μ gf 2)
    (h41 : Assumption41 P μ ξ)
    (hε : 0 < ε) :
    ∃ γ0 : ℝ, 0 < γ0 ∧ ∀ R : ℝ, 0 < R →
      IsUnifIntegrable P (fun (i : ℕ × Set.Ioc (0 : ℝ) γ0) (ω : Ω) =>
        truncIncr gf αbar βbar ε (i.2 : ℝ) R x0 (fun n => ξ n ω) i.1) := by sorry

end AdamDyn.ConstStep
