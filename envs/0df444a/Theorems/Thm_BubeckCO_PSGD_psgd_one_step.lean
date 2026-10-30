-- Prove2me | Theorems.Thm_BubeckCO_PSGD_psgd_one_step
-- name    : BubeckCO.PSGD.psgd_one_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:26:42.841929+00:00
-- url     : https://prove2.me/theorems/772695db-b46a-4bf6-ab65-808c92d09edc
-- title:
--   Proof of Theorem 3.2, first display — one-step chain of projected subgradient descent
-- statement:
--   Let $X \subseteq \mathbb{R}^n$, $f : X \to \mathbb{R}$, a step size $\eta > 0$, a point $x_s \in X$ with a subgradient $g_s \in \partial f(x_s)$ (Definition 1.2), and $y_{s+1} = x_s - \eta g_s$ as in (3.2). Then for every $x^* \in X$,
--
--   $$
--   \begin{aligned}
--   f(x_s) - f(x^*) &\le g_s^\top (x_s - x^*) \\
--   &= \tfrac{1}{\eta}\,(x_s - y_{s+1})^\top (x_s - x^*) \\
--   &= \tfrac{1}{2\eta}\big(\|x_s - x^*\|^2 + \|x_s - y_{s+1}\|^2 - \|y_{s+1} - x^*\|^2\big) \\
--   &= \tfrac{1}{2\eta}\big(\|x_s - x^*\|^2 - \|y_{s+1} - x^*\|^2\big) + \tfrac{\eta}{2}\|g_s\|^2 .
--   \end{aligned}
--   $$
--
--   This per-step estimate is the first step of the proof of Theorem 3.2; combined with Lemma 3.1 and summed over $s$ it gives the bound on $\sum_s (f(x_s) - f(x^*))$.
--
--   **Formalization Note** The chain is stated as a conjunction of one inequality and three equalities. $\eta > 0$ is the book's step-size convention (p. 262); the second link would be false at $\eta = 0$ under Lean's convention $1/0 = 0$.
--
--   Differences from the source:
--   - encoding: f : X → ℝ → f : ℝⁿ → ℝ (values off X never read); reason: Lean functions are total; every hypothesis and the conclusion evaluate f only at points of X, so the instances are the same
--   - generalization: X ⊂ ℝⁿ compact and convex (Chapter 3 standing assumption) → X an arbitrary subset of ℝⁿ; reason: the chain uses only the subgradient inequality at x* ∈ X and algebraic identities; the Chapter 3 case is a special case
--   - generalization: x* a minimizer of f on X (Notation, p. 242) → any point xstar ∈ X; reason: minimality of x* is not used; taking xstar to be the minimizer recovers the book's statement
--   - encoding: y_{s+1} defined by (3.2) → binder ys with hys : ys = xs − η • gs; reason: the same point, named as in the display
-- source:
--   Bubeck, Convex Optimization: Algorithms and Complexity, Found. Trends Mach. Learn. 8(3-4), 2015, p. 265 (PDF p. 38), proof of Theorem 3.2, first display (unnumbered)

import Mathlib
import Definitions.Def_BubeckCO_PSGD_IsSubgradient

namespace BubeckCO.PSGD

/-- **One-step chain of projected subgradient descent (proof of Theorem 3.2, first display).**
Bubeck, Convex Optimization: Algorithms and Complexity, Found. Trends Mach. Learn. 8(3-4), 2015,
p. 265 (PDF p. 38), proof of Theorem 3.2, first display:
`f(x_s) − f(x*) ≤ g_sᵀ(x_s − x*) = (1/η)(x_s − y_{s+1})ᵀ(x_s − x*)
 = (1/(2η))(‖x_s − x*‖² + ‖x_s − y_{s+1}‖² − ‖y_{s+1} − x*‖²)
 = (1/(2η))(‖x_s − x*‖² − ‖y_{s+1} − x*‖²) + (η/2)‖g_s‖²`.

For a step size `η > 0`, a subgradient `g_s ∈ ∂f(x_s)` (Definition 1.2, relative to `X`),
`y_{s+1} = x_s − η g_s` (equation (3.2)) and any `x* ∈ X`, the inequality and the three
equalities of the chain hold.

**Formalization Note.** The chain is stated as a conjunction of its four links. `X` is an
arbitrary set: the compactness and convexity of Chapter 3 are not needed for this step.
`x*` may be any point of `X` (the chain does not use minimality). `η > 0` is the book's step-size
convention (p. 262); the second link is false at `η = 0` with Lean's `1 / 0 = 0`. -/
theorem psgd_one_step {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (η : ℝ) (hη : 0 < η)
    (xs gs ys xstar : EuclideanSpace ℝ (Fin n))
    (hgs : IsSubgradient X f xs gs) (hys : ys = xs - η • gs) (hxstar : xstar ∈ X) :
    f xs - f xstar ≤ inner ℝ gs (xs - xstar) ∧
      inner ℝ gs (xs - xstar) = 1 / η * inner ℝ (xs - ys) (xs - xstar) ∧
      1 / η * inner ℝ (xs - ys) (xs - xstar) =
        1 / (2 * η) * (‖xs - xstar‖ ^ 2 + ‖xs - ys‖ ^ 2 - ‖ys - xstar‖ ^ 2) ∧
      1 / (2 * η) * (‖xs - xstar‖ ^ 2 + ‖xs - ys‖ ^ 2 - ‖ys - xstar‖ ^ 2) =
        1 / (2 * η) * (‖xs - xstar‖ ^ 2 - ‖ys - xstar‖ ^ 2) + η / 2 * ‖gs‖ ^ 2 := by sorry

end BubeckCO.PSGD
