-- Prove2me | Theorems.Thm_BubeckCO_PSGD_first_order_optimality_iff
-- name    : BubeckCO.PSGD.first_order_optimality_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:25:49.76922+00:00
-- url     : https://prove2.me/theorems/f0c41a7e-8105-4777-8d8f-9eafa8e68ed6
-- title:
--   Proposition 1.3 — first-order optimality condition on a closed convex set
-- statement:
--   Let $X \subseteq \mathbb{R}^n$ be a closed convex set, let $f$ be convex on $X$ and differentiable at every point of $X$, and let $x^* \in X$. Then $x^*$ minimizes $f$ over $X$ if and only if
--
--   $$
--   \nabla f(x^*)^\top (x^* - y) \le 0 \qquad \text{for all } y \in X .
--   $$
--
--   This is the variational-inequality characterization of constrained minimizers of differentiable convex functions; Lemma 3.1 on Euclidean projections is a corollary of it.
--
--   **Formalization Note** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`, $\nabla$ is Mathlib's `gradient`, and the minimality of $x^*$ is `IsMinOn f X xstar`. Both directions of the equivalence are stated. The sign convention is the book's.
--
--   Differences from the source:
--   - generalization: f convex → ConvexOn ℝ X f (convexity on X only); reason: a function convex on ℝⁿ or on any convex set containing X is convex on X, so the book's hypothesis implies the Lean one
--   - reading: X a closed convex set on which f is differentiable → DifferentiableAt ℝ f x at every x ∈ X, for f : ℝⁿ → ℝ; reason: ∇f(x*) must be the gradient of f in ℝⁿ also at boundary points of X, which needs f defined and differentiable around each point of X
--   - reading: x* ∈ argmin_{x∈X} f(x) ⟺ ∇f(x*)ᵀ(x* − y) ≤ 0 ∀y ∈ X, with x* unrestricted → binder xstar ∈ X; IsMinOn f X xstar ↔ ∀ y ∈ X, ⟪∇f(xstar), xstar − y⟫ ≤ 0; reason: the book's x* is always a point of X (Notation, p. 242); without it the right-hand side does not imply membership and the 'if' direction would fail for points outside X
-- source:
--   Bubeck, Convex Optimization: Algorithms and Complexity, Found. Trends Mach. Learn. 8(3-4), 2015, p. 238 (PDF p. 11), Proposition 1.3 (First order optimality condition)

import Mathlib

namespace BubeckCO.PSGD

/-- **Proposition 1.3 (first order optimality condition).**
Bubeck, Convex Optimization: Algorithms and Complexity, Found. Trends Mach. Learn. 8(3-4), 2015,
p. 238 (PDF p. 11), Proposition 1.3: "Let `f` be convex and `X` a closed convex set on which `f`
is differentiable. Then `x* ∈ argmin_{x ∈ X} f(x)`, if and only if one has
`∇f(x*)ᵀ(x* − y) ≤ 0, ∀ y ∈ X`."

For a closed convex `X ⊆ ℝⁿ`, a function `f` convex on `X` and differentiable at every point of
`X`, and a point `x* ∈ X`: `x*` minimizes `f` over `X` iff `⟪∇f(x*), x* − y⟫ ≤ 0` for all `y ∈ X`.

**Formalization Note.** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`, `∇` is Mathlib's `gradient`, and
"differentiable on `X`" is read as `DifferentiableAt` (in `ℝⁿ`) at every point of `X`, so that
`∇f(x*)` is the gradient of `f : ℝⁿ → ℝ`. Convexity is required on `X` only. `x* ∈ X` is a
binder (the book's `x*` is always a point of `X`, p. 242); Mathlib's `IsMinOn f X x*` is the
minimality part of `x* ∈ argmin_{x∈X} f(x)`. The sign convention is the book's,
`∇f(x*)ᵀ(x* − y) ≤ 0`. -/
theorem first_order_optimality_iff {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXclosed : IsClosed X) (hXconv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hfconv : ConvexOn ℝ X f)
    (hfdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X) :
    IsMinOn f X xstar ↔ ∀ y ∈ X, inner ℝ (gradient f xstar) (xstar - y) ≤ 0 := by sorry

end BubeckCO.PSGD
