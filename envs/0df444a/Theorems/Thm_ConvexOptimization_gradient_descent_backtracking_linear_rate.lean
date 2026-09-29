-- Prove2me | Theorems.Thm_ConvexOptimization_gradient_descent_backtracking_linear_rate
-- name    : ConvexOptimization.gradient_descent_backtracking_linear_rate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T15:27:31.869108+00:00
-- url     : https://prove2.me/theorems/8687d62f-90f3-4c70-8291-3d774b2ead5e
-- title:
--   Gradient descent with backtracking: linear rate
-- statement:
--   **Linear convergence of gradient descent with backtracking line search.**
--
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be $m$-strongly convex and $M$-smooth in the sense of the two-sided quadratic bounds
--
--   $$f(x) + \langle \nabla f(x), y - x\rangle + \frac{m}{2}\lVert y - x\rVert_2^2 \;\le\; f(y) \;\le\; f(x) + \langle \nabla f(x), y - x\rangle + \frac{M}{2}\lVert y - x\rVert_2^2,$$
--
--   with $0 < m \le M$, let $x^{\star}$ be a global minimizer and $p^{\star} = f(x^{\star})$. Fix backtracking parameters $\alpha \in (0, 1/2)$ and $\beta \in (0,1)$, and let $(x_k)$ satisfy $x_{k+1} = x_k - t_k \nabla f(x_k)$ where each $t_k$ is a backtracking step at $x_k$ along $-\nabla f(x_k)$. Then for every $k$
--
--   $$f(x_k) - p^{\star} \;\le\; c^{\,k}\bigl(f(x_0) - p^{\star}\bigr), \qquad c \;=\; 1 - \min\Bigl\{2m\alpha,\; \frac{2\beta\alpha m}{M}\Bigr\}.$$
--
--   The rate is again geometric, with the constant degraded from the exact-line-search value $1 - m/M$ by the two line-search parameters only; in particular the practical algorithm, which performs no one-dimensional optimization, keeps the same asymptotic behaviour. The two terms in the minimum correspond to the two possible outcomes of the search — the unit step being accepted, or a genuine backtrack.
--
--   **Formalization Note** The step sizes are governed by the mission's backtracking predicate, so the statement covers every admissible run rather than one implementation. Constants are exactly those printed in the book, with no rounding or simplification. Source: B&V §9.3.1, pp. 468–469.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 468-469, §9.3.1 (gradient descent with backtracking line search: linear convergence with c = 1 - min{2 m alpha, 2 beta alpha m / M})

import Mathlib
import Definitions.Def_ConvexOptimization_IsBacktrackingStep

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.gradient_descent_backtracking_linear_rate {n : ℕ} (m M α β : ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (hα0 : 0 < α) (hα : α < 1 / 2)
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hsc : ∀ x y : EuclideanSpace ℝ (Fin n),
      f x + ⟪g x, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hsm : ∀ x y : EuclideanSpace ℝ (Fin n),
      f y ≤ f x + ⟪g x, y - x⟫ + M / 2 * ‖y - x‖ ^ 2)
    (xstar : EuclideanSpace ℝ (Fin n)) (hstar : IsMinOn f Set.univ xstar)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hstep : ∀ k, ∃ t : ℝ,
      IsBacktrackingStep f g α β (x k) (-g (x k)) t ∧
      x (k + 1) = x k - t • g (x k)) :
    ∀ k, f (x k) - f xstar ≤
      (1 - min (2 * m * α) (2 * β * α * m / M)) ^ k * (f (x 0) - f xstar) := by
  sorry
