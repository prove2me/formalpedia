-- Prove2me | Theorems.Thm_ConvexOptAlg_FrankWolfe_eq_3_4
-- name    : ConvexOptAlg.FrankWolfe.eq_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:22:41.859988+00:00
-- url     : https://prove2.me/theorems/20b987df-eab1-4f07-8dad-32782b7f6dcb
-- title:
--   Eq. (3.4), p. 267, in an arbitrary norm (p. 272) — 0 ≤ f(x) − f(y) − ∇f(y)⊤(x − y) ≤ (β/2)‖x − y‖²
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $\mathcal X\subseteq E$ convex, and $f:E\to\mathbb R$ differentiable, convex on $\mathcal X$, and $\beta$-smooth with respect to $\|\cdot\|$ on $\mathcal X$, i.e. $\|\nabla f(x)-\nabla f(y)\|_*\le\beta\|x-y\|$ for $x,y\in\mathcal X$, where $\|\cdot\|_*$ is the dual norm. Then for all $x,y\in\mathcal X$,
--   $$0\le f(x)-f(y)-\nabla f(y)^\top(x-y)\le\frac{\beta}{2}\|x-y\|^2 .$$
--
--   This is inequality (3.4) of Section 3.2, which the book proves for the Euclidean norm and then uses in the proof of Theorem 3.8 with the remark that it holds for smoothness in an arbitrary norm. Its upper half is the first step of the one-step analysis of conditional gradient descent.
--
--   **Formalization Note** $\nabla f(y)^\top v$ is `f' y v` for a derivative map `f'` with `HasFDerivAt f (f' y) y`, and $\|\cdot\|_*$ is the operator norm. Convexity and smoothness are assumed on the convex set $\mathcal X$ and the inequality is stated for $x,y\in\mathcal X$; the book states (3.4) for all of $\mathbb R^n$, which is the case $\mathcal X=E$.
-- source:
--   Bubeck, arXiv:1405.4980v2, Eq. (3.4), p. 267; proof of Theorem 3.8, p. 272 ("it can easily be seen that (3.4) holds true for smoothness in an arbitrary norm")

import Mathlib
import Definitions.Def_ConvexOptAlg_FrankWolfe_Defs

namespace ConvexOptAlg.FrankWolfe

/-- Bubeck, arXiv:1405.4980v2, Eq. (3.4), p. 267, in an arbitrary norm as used in the proof of
Theorem 3.8, p. 272 ("it can easily be seen that (3.4) holds true for smoothness in an arbitrary
norm"): if `f` is convex and β-smooth w.r.t. `‖·‖` on the convex set `X`, then for `x, y ∈ X`,
`0 ≤ f(x) − f(y) − ∇f(y)⊤(x − y) ≤ (β/2)‖x − y‖²`. The pairing `∇f(y)⊤v` is `f' y v` and the
dual norm is the operator norm. -/
theorem eq_3_4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (hXconv : Convex ℝ X)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ)
    (hf : ConvexOn ℝ X f) (hsmooth : IsBetaSmoothNormOn X f f' β)
    (x y : E) (hx : x ∈ X) (hy : y ∈ X) :
    0 ≤ f x - f y - f' y (x - y) ∧ f x - f y - f' y (x - y) ≤ β / 2 * ‖x - y‖ ^ 2 := by sorry

end ConvexOptAlg.FrankWolfe
