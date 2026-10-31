-- Prove2me | Theorems.Thm_AccelSGDGrowth_lemma_2_2
-- name    : AccelSGDGrowth.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:09.17919+00:00
-- url     : https://prove2.me/theorems/d4fba275-467b-40ff-bd96-17a78bdac952
-- title:
--   Lemma 2.2 — consequences of convexity and $\mathcal L$-smoothness
-- statement:
--   Let $\mathcal L>0$ and $f\in\mathcal F(0,\mathcal L)$, i.e. $f$ is continuously differentiable, convex and satisfies the upper quadratic bound of (1.2). Then for all $x,y\in\mathbb R^d$:
--
--   1. $\|\nabla f(y)-\nabla f(x)\|\le\mathcal L\|y-x\|$;
--   2. $f(y)\ge f(x)+\nabla f(x)^\top(y-x)+\dfrac{\|\nabla f(y)-\nabla f(x)\|^2}{2\mathcal L}$;
--   3. $(\nabla f(y)-\nabla f(x))^\top(y-x)\ge\|\nabla f(y)-\nabla f(x)\|^2/\mathcal L$;
--   4. $(\nabla f(y)-\nabla f(x))^\top(y-x)\le\mathcal L\|y-x\|^2$.
--
--   Clause 1 (Lipschitz gradient) is what makes $\mathbb E\|\nabla f(x_k)\|^2$ finite along the algorithm.
--
--   Differences from the source:
--   - encoding: f ∈ F(0, L), L the smoothness constant → 0 < L as a hypothesis; reason: the page divides by 2L and by L
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, Lemma 2.2, pp.5–6

import Definitions.Def_AccelSGDGrowth_ClassF

namespace AccelSGDGrowth

/-- Chen, Na, Kolar, arXiv:2006.06782v4, Lemma 2.2, pp.5–6. For `f ∈ F(0, L)` with `L > 0` and all
`x, y`:
(a) `‖∇f(y) − ∇f(x)‖ ≤ L‖y − x‖`;
(b) `f(y) ≥ f(x) + ∇f(x)ᵀ(y − x) + ‖∇f(y) − ∇f(x)‖²/(2L)`;
(c) `(∇f(y) − ∇f(x))ᵀ(y − x) ≥ ‖∇f(y) − ∇f(x)‖²/L`;
(d) `(∇f(y) − ∇f(x))ᵀ(y − x) ≤ L‖y − x‖²`.

**Formalization Note.** `F(0, L)` is `ClassF 0 L f`: (1.2) with `m = 0`, i.e. convexity plus the
quadratic upper bound. `L > 0` is the smoothness constant the page divides by. -/
theorem lemma_2_2 {d : ℕ} {L : ℝ} (hL : 0 < L) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ClassF 0 L f) :
    (∀ x y : EuclideanSpace ℝ (Fin d),
      ‖gradient f y - gradient f x‖ ≤ L * ‖y - x‖) ∧
    (∀ x y : EuclideanSpace ℝ (Fin d),
      f x + inner ℝ (gradient f x) (y - x) + ‖gradient f y - gradient f x‖ ^ 2 / (2 * L) ≤ f y) ∧
    (∀ x y : EuclideanSpace ℝ (Fin d),
      ‖gradient f y - gradient f x‖ ^ 2 / L ≤ inner ℝ (gradient f y - gradient f x) (y - x)) ∧
    (∀ x y : EuclideanSpace ℝ (Fin d),
      inner ℝ (gradient f y - gradient f x) (y - x) ≤ L * ‖y - x‖ ^ 2) := by sorry

end AccelSGDGrowth
