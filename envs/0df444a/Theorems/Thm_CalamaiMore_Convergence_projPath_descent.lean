-- Prove2me | Theorems.Thm_CalamaiMore_Convergence_projPath_descent
-- name    : CalamaiMore.Convergence.projPath_descent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:30:50.355765+00:00
-- url     : https://prove2.me/theorems/9eed4feb-c748-422d-bca3-7efda5072b0f
-- title:
--   Eq. (2.4) — the projected path is a descent path
-- statement:
--   Let $\Omega$ be a nonempty closed convex subset of a finite-dimensional real inner product space $E$, $P$ the projection into $\Omega$, and $f : E \to \mathbb R$ continuously differentiable on $\Omega$. For $x \in \Omega$ let $x(\alpha) = P(x - \alpha\nabla f(x))$. Then for every $\alpha > 0$,
--
--   $$
--   \langle \nabla f(x), x - x(\alpha) \rangle \ge \frac{\|x(\alpha) - x\|^2}{\alpha}.
--   $$
--
--   In particular the step from $x$ to $x(\alpha)$ is a descent direction whenever $x(\alpha) \neq x$; the estimate is used with $x = x_k$ throughout the convergence analysis.
--
--   **Formalization Note** "Continuously differentiable on $\Omega$" is $f$ differentiable at every point of $\Omega$ with $\nabla f$ continuous on $\Omega$ (the paper's standing assumption for §2).
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 98, Eq. (2.4)

import Mathlib
import Definitions.Def_CalamaiMore_Convergence_IsGradientProjectionRun

namespace CalamaiMore.Convergence

/-- Calamai–Moré, Eq. (2.4) (p. 98): for `x ∈ Ω` and `α > 0`,
`⟨∇f(x), x - x(α)⟩ ≥ ‖x(α) - x‖² / α` where `x(α) = P(x - α ∇f(x))`. -/
theorem projPath_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (hΩcv : Convex ℝ Ω)
    (f : E → ℝ) (hfd : ∀ x ∈ Ω, DifferentiableAt ℝ f x) (hfc : ContinuousOn (gradient f) Ω)
    (x : E) (hx : x ∈ Ω) (α : ℝ) (hα : 0 < α) :
    ‖projPath f Ω x α - x‖ ^ 2 / α ≤ inner ℝ (gradient f x) (x - projPath f Ω x α) := by sorry

end CalamaiMore.Convergence
