-- Prove2me | Theorems.Thm_ConvexOptAlg_LowerBounds_theorem_3_14
-- name    : ConvexOptAlg.LowerBounds.theorem_3_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:44:53.597798+00:00
-- url     : https://prove2.me/theorems/06567be9-c958-4f28-8a28-85880f487677
-- title:
--   Theorem 3.14, p. 282 — some β-smooth convex f forces min_{s≤t} f(x_s) − f(x*) ≥ (3β/32)‖x₁ − x*‖²/(t + 1)² under (3.15)
-- statement:
--   Let $n,t$ be integers with $1\le t\le\frac{n-1}2$ and let $\beta>0$. There exist a $\beta$-smooth convex function $f:\mathbb R^n\to\mathbb R$ and a minimizer $x^*$ of $f$ such that for every black-box procedure satisfying (3.15) — $x_1=0$ and $x_{s+1}\in\mathrm{Span}(\nabla f(x_1),\dots,\nabla f(x_s))$ — one has
--   $$\min_{1\le s\le t}f(x_s)-f(x^*)\ \ge\ \frac{3\beta}{32}\,\frac{\|x_1-x^*\|^2}{(t+1)^2}.$$
--
--   Together with the $O(\beta\|x_1-x^*\|^2/t^2)$ upper bound of Nesterov's accelerated gradient descent, this shows that the accelerated rate is optimal, up to a numerical constant, among first-order methods of the form (3.15) when the number of queries is at most about half the dimension.
--
--   **Formalization Note** The function $f$, its gradient map $g$ and the minimizer $x^*$ are chosen before the procedure (an $\exists\,\forall$ statement); $\beta$-smoothness means $g=\nabla f$ everywhere and $g$ is $\beta$-Lipschitz. The book writes $f(x^*)$ for a minimizer whose existence it always assumes; the hard function has many minimizers when $2t+1<n$, and the statement asserts the bound for one of them, as in the book's proof. The minimum over $1\le s\le t$ is written as the bound for every such $s$, and $t\ge1$ is added so that this minimum is over a nonempty range. The hypothesis $t\le(n-1)/2$ is written $2t+1\le n$.
-- source:
--   Bubeck, arXiv:1405.4980v2, Theorem 3.14, p. 282

import Mathlib
import Definitions.Def_ConvexOptAlg_LowerBounds_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.LowerBounds

/-- Bubeck, arXiv:1405.4980v2, Theorem 3.14, p. 282. Let `t ≤ (n − 1)/2` (i.e. `2t + 1 ≤ n`), `t ≥ 1`,
`β > 0`. There exist a β-smooth convex `f : ℝⁿ → ℝ` (with gradient map `g`) and a minimizer `x*` of
`f` such that every black-box procedure satisfying (3.15) for the gradient oracle `g` has
`min_{1≤s≤t} f(x_s) − f(x*) ≥ (3β/32) ‖x₁ − x*‖²/(t + 1)²`, i.e. the bound holds for every
`s ∈ [1, t]`. The function and the minimizer are chosen before the procedure. -/
theorem theorem_3_14 (n t : ℕ) (β : ℝ) (ht : 1 ≤ t) (htn : 2 * t + 1 ≤ n) (hβ : 0 < β) :
    ∃ (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      (∀ y, HasGradientAt f (g y) y) ∧ IsBetaSmooth g β ∧ ConvexOn ℝ Set.univ f ∧
        ∃ xstar : EuclideanSpace ℝ (Fin n), (∀ y, f xstar ≤ f y) ∧
          ∀ x : ℕ → EuclideanSpace ℝ (Fin n), SatisfiesSpanCondition g x →
            ∀ s ∈ Finset.Icc 1 t,
              f (x s) - f xstar ≥ 3 * β / 32 * (‖x 1 - xstar‖ ^ 2 / ((t : ℝ) + 1) ^ 2) := by sorry

end ConvexOptAlg.LowerBounds
