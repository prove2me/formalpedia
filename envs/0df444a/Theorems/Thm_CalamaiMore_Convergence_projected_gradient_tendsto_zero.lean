-- Prove2me | Theorems.Thm_CalamaiMore_Convergence_projected_gradient_tendsto_zero
-- name    : CalamaiMore.Convergence.projected_gradient_tendsto_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:35:29.193+00:00
-- url     : https://prove2.me/theorems/d4d16490-bcec-4b85-80c1-d0d79ff9093d
-- title:
--   Theorem 3.2 — the gradient projection method drives $\|\nabla_\Omega f(x_k)\|$ to zero
-- statement:
--   Let $\Omega$ be a nonempty closed convex subset of a finite-dimensional real inner product space $E$, and let $f : E \to \mathbb R$ be continuously differentiable on $\Omega$. Let $(x_k, \alpha_k)$ be a run of the gradient projection method defined by (2.1) and (2.2), with constants $\gamma_1, \gamma_2 > 0$ and $\mu_1, \mu_2 \in (0,1)$, whose steps satisfy
--
--   $$
--   \alpha_k \le \gamma_3 \qquad (3.2)
--   $$
--
--   for some constant $\gamma_3$. If $f$ is bounded below on $\Omega$ and $\nabla f$ is uniformly continuous on $\Omega$, then the projected gradients converge to zero:
--
--   $$
--   \lim_{k \to \infty} \|\nabla_\Omega f(x_k)\| = 0.
--   $$
--
--   No boundedness of the iterates is assumed. Since $\nabla_\Omega f(x) = 0$ exactly at stationary points and $\|\nabla_\Omega f(\cdot)\|$ is lower semicontinuous, the theorem implies that every limit point of the iterates is stationary; it is also the hypothesis under which the active constraints are identified in finitely many steps for polyhedral $\Omega$.
--
--   **Formalization Note** "Continuously differentiable on $\Omega$" is $f$ differentiable at every point of $\Omega$ with $\nabla f$ continuous on $\Omega$; "bounded below on $\Omega$" is `BddBelow (f '' Ω)`; $\nabla_\Omega f$ is the `projGrad` of this mission, taken at the iterates, which lie in $\Omega$.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 103, Theorem 3.2

import Mathlib
import Definitions.Def_CalamaiMore_Convergence_projGrad
import Definitions.Def_CalamaiMore_Convergence_IsGradientProjectionRun

namespace CalamaiMore.Convergence

/-- Calamai–Moré, Theorem 3.2 (p. 103): with bounded steps `α_k ≤ γ₃` (3.2), if `f` is bounded
below on `Ω` and `∇f` is uniformly continuous on `Ω`, then `‖∇_Ω f(x_k)‖ → 0`. -/
theorem projected_gradient_tendsto_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (hΩcv : Convex ℝ Ω)
    (f : E → ℝ) (hfd : ∀ x ∈ Ω, DifferentiableAt ℝ f x) (hfc : ContinuousOn (gradient f) Ω)
    (γ₁ γ₂ μ₁ μ₂ : ℝ) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hμ₁ : μ₁ ∈ Set.Ioo (0 : ℝ) 1) (hμ₂ : μ₂ ∈ Set.Ioo (0 : ℝ) 1)
    (x : ℕ → E) (α : ℕ → ℝ) (hrun : IsGradientProjectionRun f Ω γ₁ γ₂ μ₁ μ₂ x α)
    (γ₃ : ℝ) (hα₃ : ∀ k, α k ≤ γ₃)
    (hbdd : BddBelow (f '' Ω)) (huc : UniformContinuousOn (gradient f) Ω) :
    Filter.Tendsto (fun k => ‖projGrad f Ω (x k)‖) Filter.atTop (nhds 0) := by sorry

end CalamaiMore.Convergence
