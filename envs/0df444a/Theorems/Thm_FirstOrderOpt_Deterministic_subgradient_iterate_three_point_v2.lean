-- Prove2me | Theorems.Thm_FirstOrderOpt_Deterministic_subgradient_iterate_three_point_v2
-- name    : FirstOrderOpt.Deterministic.subgradient_iterate_three_point_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:16:32.218977+00:00
-- url     : https://prove2.me/theorems/cdc7f712-c31a-455b-a249-d88aa2f6c1ab
-- title:
--   Lemma 3.1 — three-point inequality for the projected-subgradient step (corrected: closed convex $X$)
-- statement:
--   Let $X$ be a closed convex subset of a real inner-product space, $x_t\in X$, $g_t$ a vector (a subgradient of $f$ at $x_t$) and $\gamma_t\in\mathbb R$. If $x_{t+1}\in X$ minimizes $x\mapsto\gamma_t\langle g_t,x\rangle+\tfrac12\|x-x_t\|^2$ over $X$ (the projected-subgradient step (3.1.3) in its equivalent form (3.1.4)), then for every $x\in X$
--   $$\gamma_t\langle g_t,x_{t+1}-x\rangle+\tfrac12\|x_{t+1}-x_t\|^2\le\tfrac12\|x-x_t\|^2-\tfrac12\|x-x_{t+1}\|^2.$$
--
--   **Formalization Note.** The retired statement omitted the chapter's standing assumption that $X$ is closed and convex; the lemma passes from minimality to the first-order optimality condition $\langle\gamma_tg_t+x_{t+1}-x_t,x-x_{t+1}\rangle\ge 0$, which needs convexity of $X$ (disproved on a non-convex $X$). The book quantifies over $y\in X$ but uses $x$ in the body; it is read as a single free variable $x\in X$.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 53, Lemma 3.1

import Mathlib

namespace FirstOrderOpt.Deterministic

open scoped RealInnerProductSpace

/-- Lemma 3.1 (three-point inequality for the projected-subgradient update), Lan p. 53. Let
`X` be the closed convex feasible set of §3.1. Given `xt` and a subgradient `gt` of `f` at `xt`,
let `xt1` minimize `x ↦ γt⟨gt, x⟩ + ‖x - xt‖²/2` over `X` (the projected-subgradient step (3.1.3)
in its equivalent form (3.1.4)). Then for every `x ∈ X`,
`γt⟨gt, xt1 - x⟩ + ‖xt1 - xt‖²/2 ≤ ‖x - xt‖²/2 - ‖x - xt1‖²/2`.

Corrected version: the retired statement dropped the standing assumption that `X` is closed and
convex (the first-order optimality condition of the step needs convexity of `X`). The book's
statement quantifies over `y ∈ X` but uses `x` in the body; read as a single free variable. -/
theorem subgradient_iterate_three_point_v2 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (xt xt1 gt : E) (γt : ℝ)
    (hxt : xt ∈ X) (hxt1 : xt1 ∈ X)
    (hmin : ∀ x ∈ X, γt * ⟪gt, xt1⟫ + (1 / 2) * ‖xt1 - xt‖ ^ 2 ≤
      γt * ⟪gt, x⟫ + (1 / 2) * ‖x - xt‖ ^ 2) :
    ∀ x ∈ X, γt * ⟪gt, xt1 - x⟫ + (1 / 2) * ‖xt1 - xt‖ ^ 2 ≤
      (1 / 2) * ‖x - xt‖ ^ 2 - (1 / 2) * ‖x - xt1‖ ^ 2 := by sorry

end FirstOrderOpt.Deterministic
