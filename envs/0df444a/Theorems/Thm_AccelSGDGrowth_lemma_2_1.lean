-- Prove2me | Theorems.Thm_AccelSGDGrowth_lemma_2_1
-- name    : AccelSGDGrowth.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:23.218567+00:00
-- url     : https://prove2.me/theorems/b587e80f-8e1a-42d4-8677-679481d9d722
-- title:
--   Lemma 2.1 — consequences of $m$-strong convexity
-- statement:
--   Let $m>0$ and $f\in\mathcal F(m,\infty)$, i.e. $f$ is continuously differentiable and $m$-strongly convex in the sense of (1.2). Then for all $x,y\in\mathbb R^d$:
--
--   1. $f(y)\le f(x)+\nabla f(x)^\top(y-x)+\dfrac{\|\nabla f(y)-\nabla f(x)\|^2}{2m}$;
--   2. $(\nabla f(y)-\nabla f(x))^\top(y-x)\ge m\|y-x\|^2$;
--   3. $\|\nabla f(y)-\nabla f(x)\|\ge m\|y-x\|$.
--
--   Clause 1 at a minimizer gives $f(x)-f(x_\star)\le\|\nabla f(x)\|^2/(2m)$, the step of Theorem 5.1 that turns gradient bounds into function-value bounds.
--
--   Differences from the source:
--   - encoding: f ∈ F(m, ∞), m the strong-convexity modulus → 0 < m as a hypothesis; reason: the page divides by 2m and calls f m-strongly convex; m ≤ 0 is not a strong-convexity modulus
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, Lemma 2.1, p.5

import Definitions.Def_AccelSGDGrowth_ClassFInf

namespace AccelSGDGrowth

/-- Chen, Na, Kolar, arXiv:2006.06782v4, Lemma 2.1, p.5. For `f ∈ F(m, ∞)` with `m > 0` and all
`x, y`:
(a) `f(y) ≤ f(x) + ∇f(x)ᵀ(y − x) + ‖∇f(y) − ∇f(x)‖²/(2m)`;
(b) `(∇f(y) − ∇f(x))ᵀ(y − x) ≥ m‖y − x‖²`;
(c) `‖∇f(y) − ∇f(x)‖ ≥ m‖y − x‖`.

**Formalization Note.** `m > 0` is the strong-convexity modulus the page divides by in (a). -/
theorem lemma_2_1 {d : ℕ} {m : ℝ} (hm : 0 < m) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ClassFInf m f) :
    (∀ x y : EuclideanSpace ℝ (Fin d),
      f y ≤ f x + inner ℝ (gradient f x) (y - x) +
        ‖gradient f y - gradient f x‖ ^ 2 / (2 * m)) ∧
    (∀ x y : EuclideanSpace ℝ (Fin d),
      m * ‖y - x‖ ^ 2 ≤ inner ℝ (gradient f y - gradient f x) (y - x)) ∧
    (∀ x y : EuclideanSpace ℝ (Fin d),
      m * ‖y - x‖ ≤ ‖gradient f y - gradient f x‖) := by sorry

end AccelSGDGrowth
