-- Prove2me | Theorems.Thm_ConvexOptimization_newton_quadratic_phase_contraction
-- name    : ConvexOptimization.newton_quadratic_phase_contraction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T15:28:22.874255+00:00
-- url     : https://prove2.me/theorems/4e501866-1403-49d3-8632-f7480216bdc0
-- title:
--   Newton quadratic-phase contraction
-- statement:
--   **The quadratically convergent phase: the scaled gradient norm squares at every step** — inequality (9.33) of Boyd & Vandenberghe.
--
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be twice differentiable and assume, for constants $0 < m \le M$ and $L > 0$,
--
--   $$m I \preceq \nabla^2 f(x) \preceq M I, \qquad \lVert \nabla^2 f(x) - \nabla^2 f(y)\rVert \le L\lVert x - y\rVert_2 ,$$
--
--   fix backtracking parameters $\alpha \in (0,1/2)$, $\beta \in (0,1)$, and set $\eta = \min\{1, 3(1-2\alpha)\}\,m^{2}/L$. Let $x$ satisfy $\lVert \nabla f(x)\rVert_2 < \eta$ and let $\Delta$ solve the Newton system $\nabla^2 f(x)\,\Delta = -\nabla f(x)$. Then the unit step passes the Armijo test, so backtracking accepts $t = 1$, and the next iterate $x^{+} = x + \Delta$ satisfies
--
--   $$f(x + \Delta) \le f(x) + \alpha \langle \nabla f(x), \Delta\rangle \qquad\text{and}\qquad \frac{L}{2m^{2}}\lVert \nabla f(x^{+})\rVert_2 \;\le\; \Bigl(\frac{L}{2m^{2}}\lVert \nabla f(x)\rVert_2\Bigr)^{2}.$$
--
--   Once the gradient drops below $\eta$ it never rises above it again, the method takes full Newton steps from then on, and the scaled quantity $\frac{L}{2m^2}\lVert\nabla f\rVert_2$ squares at each iteration — the number of correct digits doubles per step. This is the source of the $\log_2\log_2(\varepsilon_0/\varepsilon)$ term in the mission's goal theorem, and the precise reason Newton's method is qualitatively different from any first-order method.
--
--   **Formalization Note** The conclusion is a conjunction: acceptance of the unit step is stated as the Armijo inequality at $t = 1$ rather than by invoking the backtracking predicate, since acceptance is exactly what has to be proved. Hessian bounds are in quadratic-form guise and the Lipschitz condition uses the operator norm. Source: B&V §9.5.3, pp. 488–491, eq. (9.33).
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 488-491, §9.5.3 eq. (9.33) (quadratically convergent phase: the scaled gradient norm squares and the unit step is accepted)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.newton_quadratic_phase_contraction {n : ℕ} (m M L α β η : ℝ)
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
    (x Δ : EuclideanSpace ℝ (Fin n))
    (hΔ : H x Δ = -g x) (hgx : ‖g x‖ < η) :
    (f (x + Δ) ≤ f x + α * ⟪g x, Δ⟫) ∧
    L / (2 * m ^ 2) * ‖g (x + Δ)‖ ≤ (L / (2 * m ^ 2) * ‖g x‖) ^ 2 := by
  sorry
