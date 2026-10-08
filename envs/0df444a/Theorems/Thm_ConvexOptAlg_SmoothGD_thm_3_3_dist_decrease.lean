-- Prove2me | Theorems.Thm_ConvexOptAlg_SmoothGD_thm_3_3_dist_decrease
-- name    : ConvexOptAlg.SmoothGD.thm_3_3_dist_decrease
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:05:39.44297+00:00
-- url     : https://prove2.me/theorems/714c5bf9-8bee-4037-a31a-a854a957bf23
-- title:
--   §3.2, proof of Theorem 3.3, p. 269 — gradient descent with η = 1/β does not increase ‖x_s − x*‖
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex and $\beta$-smooth with $\beta>0$, and let $x^*$ be a minimizer of $f$ on $\mathbb R^n$. Let $(x_s)_{s\ge1}$ be gradient descent with step size $\eta=1/\beta$, $x_{s+1}=x_s-\frac1\beta\nabla f(x_s)$. Then for every $s\ge1$,
--
--   $$\|x_{s+1}-x^*\|^2\le\|x_s-x^*\|^2-\frac1{\beta^2}\|\nabla f(x_s)\|^2,\qquad\text{hence}\qquad \|x_{s+1}-x^*\|\le\|x_s-x^*\|.$$
--
--   This is the last step of the proof of Theorem 3.3: the distance to the minimizer is non-increasing along the iterates.
--
--   **Formalization Note** The existence of the minimizer $x^*$ is the book's standing assumption (p. 242). The fact $\nabla f(x^*)=0$ used on the page is not a hypothesis; it follows from minimality. $\beta>0$ is implicit ($\eta=1/\beta$).
-- source:
--   Bubeck, arXiv:1405.4980v2, §3.2, proof of Theorem 3.3, display on p. 269 (after (3.6))

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.SmoothGD

/-- Proof of Theorem 3.3, display on p. 269 (Bubeck, arXiv:1405.4980v2): for gradient descent with
`η = 1/β` on a convex β-smooth `f` (β > 0) with a minimizer `x*`, for every `s ≥ 1`,
`‖x_{s+1} − x*‖² ≤ ‖x_s − x*‖² − (1/β²)‖∇f(x_s)‖²` and hence `‖x_{s+1} − x*‖ ≤ ‖x_s − x*‖`. -/
theorem thm_3_3_dist_decrease {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsGDRun g (1 / β) x) (s : ℕ) (hs : 1 ≤ s) :
    ‖x (s + 1) - xstar‖ ^ 2 ≤ ‖x s - xstar‖ ^ 2 - 1 / β ^ 2 * ‖g (x s)‖ ^ 2 ∧
      ‖x (s + 1) - xstar‖ ≤ ‖x s - xstar‖ := by sorry

end ConvexOptAlg.SmoothGD
