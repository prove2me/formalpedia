-- Prove2me | Theorems.Thm_FirstOrderOpt_Deterministic_subgradient_iterate_three_point
-- name    : FirstOrderOpt.Deterministic.subgradient_iterate_three_point
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:57:04.072842+00:00
-- url     : https://prove2.me/theorems/7b92073f-7e5c-4705-b1de-f98b84ab1168
-- title:
--   Lemma 3.1 — three-point inequality for the projected-subgradient update
-- statement:
--   The projected-subgradient method minimizes $f$ over a closed convex set $X \subseteq
--   \mathbb{R}^n$ by $x_{t+1} := \arg\min_{x\in X} \|x - (x_t - \gamma_t g(x_t))\|_2^2$ for a
--   subgradient $g(x_t) \in \partial f(x_t)$ and stepsize $\gamma_t > 0$ (Eq. (3.1.3)),
--   equivalently $x_{t+1} = \arg\min_{x\in X}\ \gamma_t\langle g(x_t), x\rangle + \tfrac12\|x -
--   x_t\|_2^2$ (Eq. (3.1.4)).
--
--   **Lemma 3.1.** For every $x \in X$,
--   $$\gamma_t\langle g(x_t), x_{t+1}-x\rangle + \tfrac12\|x_{t+1}-x_t\|_2^2 \le \tfrac12\|x-x_t
--   \|_2^2 - \tfrac12\|x-x_{t+1}\|_2^2.$$
--
--   This is the basic "three-point" characterization of a proximal/projection step: it packages
--   the first-order optimality of $x_{t+1}$ into an inequality relating $x_t, x_{t+1}$ and an
--   arbitrary comparison point, and is the single fact every convergence bound for
--   (projected) subgradient descent in this chapter is built from.
--
--   **Formalization Note.** The book's own statement quantifies "for any $y \in X$" but then uses
--   the letter $x$ throughout the displayed inequality — an evident variable-reuse slip (there is
--   only one free comparison point, not two). Formalized with a single bound variable $x \in X$.
--   $x_{t+1}$'s defining property (3.1.4) is taken as the hypothesis that it minimizes $u \mapsto
--   \gamma_t\langle g(x_t), u\rangle + \tfrac12\|u-x_t\|_2^2$ over $X$, stated pointwise rather
--   than via an `argmin`/`IsMinOn` wrapper, so the lemma needs no existence or uniqueness
--   machinery for the projection itself.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 53, Lemma 3.1

import Mathlib

namespace FirstOrderOpt.Deterministic

open scoped RealInnerProductSpace

/-- Lemma 3.1 (three-point inequality for the projected-subgradient update). Given `xt` and a
subgradient `gt` of `f` at `xt`, `xt1` minimizes `x ↦ γt⟨gt,x⟩ + ‖x-xt‖²/2` over `X` (the
equivalent form (3.1.4) of the update (3.1.3)); then for every `x ∈ X`, `γt⟨gt, xt1-x⟩ +
‖xt1-xt‖²/2 ≤ ‖x-xt‖²/2 - ‖x-xt1‖²/2`. The book's own statement quantifies over `y ∈ X` but uses
`x` in the body — read here as a single free variable `x ∈ X`, per the erratum recorded in
`STATUS.md`. -/
theorem subgradient_iterate_three_point {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (xt xt1 gt : E) (γt : ℝ)
    (hxt1 : xt1 ∈ X)
    (hmin : ∀ x ∈ X, γt * ⟪gt, xt1⟫ + (1 / 2) * ‖xt1 - xt‖ ^ 2 ≤
      γt * ⟪gt, x⟫ + (1 / 2) * ‖x - xt‖ ^ 2) :
    ∀ x ∈ X, γt * ⟪gt, xt1 - x⟫ + (1 / 2) * ‖xt1 - xt‖ ^ 2 ≤
      (1 / 2) * ‖x - xt‖ ^ 2 - (1 / 2) * ‖x - xt1‖ ^ 2 := by sorry

end FirstOrderOpt.Deterministic
