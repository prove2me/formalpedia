-- Prove2me | Theorems.Thm_CalamaiMore_Convergence_run_descent
-- name    : CalamaiMore.Convergence.run_descent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:31:23.563574+00:00
-- url     : https://prove2.me/theorems/f6e0ad63-c5b2-4f6f-a382-71ca3ff6a816
-- title:
--   Eq. (2.5) — descent estimate along a run
-- statement:
--   Let $\Omega$ be a nonempty closed convex subset of a finite-dimensional real inner product space $E$, $f : E \to \mathbb R$ continuously differentiable on $\Omega$, and let $(x_k, \alpha_k)$ be a run of the gradient projection method (2.1)–(2.3) with constants $\gamma_1, \gamma_2 > 0$ and $\mu_1, \mu_2 \in (0,1)$. Then for every $k \ge 0$,
--
--   $$
--   \langle \nabla f(x_k), x_k - x_{k+1} \rangle \ge \frac{\|x_{k+1} - x_k\|^2}{\alpha_k}.
--   $$
--
--   Combined with the sufficient decrease condition (2.1), this bounds the decrease of $f$ from below by the squared step length divided by the step.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 98, Eq. (2.5)

import Mathlib
import Definitions.Def_CalamaiMore_Convergence_IsGradientProjectionRun

namespace CalamaiMore.Convergence

/-- Calamai–Moré, Eq. (2.5) (p. 98): along a run of the gradient projection method,
`⟨∇f(x_k), x_k - x_{k+1}⟩ ≥ ‖x_{k+1} - x_k‖² / α_k` for every `k`. -/
theorem run_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (hΩcv : Convex ℝ Ω)
    (f : E → ℝ) (hfd : ∀ x ∈ Ω, DifferentiableAt ℝ f x) (hfc : ContinuousOn (gradient f) Ω)
    (γ₁ γ₂ μ₁ μ₂ : ℝ) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hμ₁ : μ₁ ∈ Set.Ioo (0 : ℝ) 1) (hμ₂ : μ₂ ∈ Set.Ioo (0 : ℝ) 1)
    (x : ℕ → E) (α : ℕ → ℝ) (hrun : IsGradientProjectionRun f Ω γ₁ γ₂ μ₁ μ₂ x α)
    (k : ℕ) :
    ‖x (k + 1) - x k‖ ^ 2 / α k ≤ inner ℝ (gradient f (x k)) (x k - x (k + 1)) := by sorry

end CalamaiMore.Convergence
