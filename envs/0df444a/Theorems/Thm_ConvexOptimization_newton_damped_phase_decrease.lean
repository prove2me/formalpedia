-- Prove2me | Theorems.Thm_ConvexOptimization_newton_damped_phase_decrease
-- name    : ConvexOptimization.newton_damped_phase_decrease
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T15:28:05.029291+00:00
-- url     : https://prove2.me/theorems/e88f2e64-3f19-4b35-b4ed-75ae85fbdb06
-- title:
--   Newton damped-phase decrease
-- statement:
--   **The damped Newton phase: a fixed decrease per iteration** — inequality (9.32) of Boyd & Vandenberghe.
--
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be twice differentiable with gradient field $\nabla f$ and Hessian field $\nabla^2 f$, and assume, for constants $0 < m \le M$ and $L > 0$,
--
--   $$m I \preceq \nabla^2 f(x) \preceq M I \quad \text{for all } x, \qquad \lVert \nabla^2 f(x) - \nabla^2 f(y)\rVert \le L \lVert x - y\rVert_2 \quad \text{for all } x, y,$$
--
--   the second being the Lipschitz-Hessian condition (9.31). Fix backtracking parameters $\alpha \in (0, 1/2)$, $\beta \in (0,1)$ and set
--
--   $$\eta \;=\; \min\{1,\, 3(1 - 2\alpha)\}\,\frac{m^{2}}{L}, \qquad \gamma \;=\; \frac{\alpha\beta\eta^{2}m}{M^{2}}.$$
--
--   Let $x$ be a point with $\lVert \nabla f(x)\rVert_2 \ge \eta$, let $\Delta$ be its Newton step, i.e. the solution of $\nabla^2 f(x)\,\Delta = -\nabla f(x)$, and let $t$ be any backtracking step at $x$ along $\Delta$. Then
--
--   $$f(x + t\Delta) \;\le\; f(x) - \gamma .$$
--
--   While the gradient stays above the threshold $\eta$, every iteration buys a decrease of at least the *constant* $\gamma$ — independent of the iterate. Since $f$ is bounded below by $p^{\star}$, this immediately caps the number of such iterations by $(f(x^{(0)}) - p^{\star})/\gamma$, which is the first of the two terms in the mission's goal theorem.
--
--   **Formalization Note** The Hessian bounds are stated in quadratic-form guise, `m * ‖v‖ ^ 2 ≤ ⟪H x v, v⟫` and `⟪H x v, v⟫ ≤ M * ‖v‖ ^ 2`, and the Lipschitz condition uses the operator norm on continuous linear maps. The Newton direction appears as a solution of the linear system, so no invertibility hypothesis is needed. Source: B&V §9.5.3, pp. 489–490, eq. (9.32).
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 489-490, §9.5.3 eq. (9.32) (damped Newton phase: each step decreases f by at least gamma = alpha beta eta^2 m / M^2, with eta = min{1, 3(1 - 2 alpha)} m^2 / L)

import Mathlib
import Definitions.Def_ConvexOptimization_IsBacktrackingStep

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.newton_damped_phase_decrease {n : ℕ} (m M L α β η : ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (hL : 0 < L)
    (hα0 : 0 < α) (hα : α < 1 / 2) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hη : η = min 1 (3 * (1 - 2 * α)) * m ^ 2 / L)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x, HasFDerivAt g (H x) x)
    (hHm : ∀ x v, m * ‖v‖ ^ 2 ≤ ⟪H x v, v⟫)
    (hHM : ∀ x v, ⟪H x v, v⟫ ≤ M * ‖v‖ ^ 2)
    (hHL : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x Δ : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (hΔ : H x Δ = -g x) (hgx : η ≤ ‖g x‖)
    (ht : IsBacktrackingStep f g α β x Δ t) :
    f (x + t • Δ) ≤ f x - α * β * η ^ 2 * m / M ^ 2 := by
  sorry
