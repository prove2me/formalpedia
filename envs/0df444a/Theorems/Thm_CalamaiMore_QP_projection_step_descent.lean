-- Prove2me | Theorems.Thm_CalamaiMore_QP_projection_step_descent
-- name    : CalamaiMore.QP.projection_step_descent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:00:04.254987+00:00
-- url     : https://prove2.me/theorems/2f7d3f38-161c-48cf-abc7-e0a49b56f6aa
-- title:
--   Eq. (2.5) — $\langle\nabla f(x_k), x_k - x_{k+1}\rangle \ge \|x_{k+1} - x_k\|^2/\alpha_k$
-- statement:
--   Let $\Omega$ be a nonempty closed convex subset of a finite-dimensional real inner product space $E$, and let $f : E \to \mathbb{R}$ be continuously differentiable on $\Omega$. Let $x_k \in \Omega$, let $\alpha_k > 0$, and let $x_{k+1} = P(x_k - \alpha_k \nabla f(x_k))$ be the gradient projection step. Then
--
--   $$
--   \langle \nabla f(x_k),\ x_k - x_{k+1} \rangle \ge \frac{\|x_{k+1} - x_k\|^2}{\alpha_k}.
--   $$
--
--   The estimate says that the step direction $x_{k+1} - x_k$ is a descent direction whenever it is nonzero; combined with the sufficient decrease condition (2.1) it shows that a gradient projection step strictly decreases $f$ unless $x_{k+1} = x_k$.
--
--   **Formalization Note** "Continuously differentiable on $\Omega$" is stated as differentiability at every point of $\Omega$ together with continuity of `gradient f` on $\Omega$, the standing assumption of Section 2 of the paper.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 98, Eq. (2.5)

import Mathlib
import Definitions.Def_CalamaiMore_QP_proj

namespace CalamaiMore.QP

/-- Calamai–Moré, Eq. (2.5) (p. 98): for a nonempty closed convex `Ω`, an iterate `x_k ∈ Ω`, a
step `α_k > 0` and `x_{k+1} = P(x_k - α_k ∇f(x_k))`,
`⟨∇f(x_k), x_k - x_{k+1}⟩ ≥ ‖x_{k+1} - x_k‖² / α_k`. -/
theorem projection_step_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (hΩcv : Convex ℝ Ω)
    (f : E → ℝ) (hfd : ∀ y ∈ Ω, DifferentiableAt ℝ f y) (hfc : ContinuousOn (gradient f) Ω)
    (xk xnext : E) (hxk : xk ∈ Ω) (αk : ℝ) (hαk : 0 < αk)
    (hstep : xnext = projPath f Ω xk αk) :
    ‖xnext - xk‖ ^ 2 / αk ≤ inner ℝ (gradient f xk) (xk - xnext) := by sorry

end CalamaiMore.QP
