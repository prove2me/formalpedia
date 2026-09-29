-- Prove2me | Theorems.Thm_CalamaiMore_Convergence_step_ratio_tendsto_zero
-- name    : CalamaiMore.Convergence.step_ratio_tendsto_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:32:34.589793+00:00
-- url     : https://prove2.me/theorems/dfb0529a-4c83-4f61-9678-80fe2b9326bb
-- title:
--   Theorem 2.3 — $\|x_{k+1} - x_k\|/\alpha_k \to 0$
-- statement:
--   Let $\Omega$ be a nonempty closed convex subset of a finite-dimensional real inner product space $E$, let $f : E \to \mathbb R$ be continuously differentiable on $\Omega$, and let $(x_k, \alpha_k)$ be a run of the gradient projection method defined by (2.1) and (2.2), with constants $\gamma_1, \gamma_2 > 0$ and $\mu_1, \mu_2 \in (0,1)$. If $f$ is bounded below on $\Omega$ and $\nabla f$ is uniformly continuous on $\Omega$, then
--
--   $$
--   \lim_{k \to \infty} \frac{\|x_{k+1} - x_k\|}{\alpha_k} = 0.
--   $$
--
--   No boundedness of the iterates $\{x_k\}$ or of the steps $\{\alpha_k\}$ is assumed. The ratio is a lower bound for $\|\nabla_\Omega f(x_k)\|$, and the theorem is the main step towards the convergence of the projected gradients (Theorem 3.2).
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 99, Theorem 2.3

import Mathlib
import Definitions.Def_CalamaiMore_Convergence_IsGradientProjectionRun

namespace CalamaiMore.Convergence

/-- Calamai–Moré, Theorem 2.3 (p. 99): if `f` is bounded below on `Ω` and `∇f` is uniformly
continuous on `Ω`, then `‖x_{k+1} - x_k‖ / α_k → 0`. -/
theorem step_ratio_tendsto_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (hΩcv : Convex ℝ Ω)
    (f : E → ℝ) (hfd : ∀ x ∈ Ω, DifferentiableAt ℝ f x) (hfc : ContinuousOn (gradient f) Ω)
    (γ₁ γ₂ μ₁ μ₂ : ℝ) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hμ₁ : μ₁ ∈ Set.Ioo (0 : ℝ) 1) (hμ₂ : μ₂ ∈ Set.Ioo (0 : ℝ) 1)
    (x : ℕ → E) (α : ℕ → ℝ) (hrun : IsGradientProjectionRun f Ω γ₁ γ₂ μ₁ μ₂ x α)
    (hbdd : BddBelow (f '' Ω)) (huc : UniformContinuousOn (gradient f) Ω) :
    Filter.Tendsto (fun k => ‖x (k + 1) - x k‖ / α k) Filter.atTop (nhds 0) := by sorry

end CalamaiMore.Convergence
