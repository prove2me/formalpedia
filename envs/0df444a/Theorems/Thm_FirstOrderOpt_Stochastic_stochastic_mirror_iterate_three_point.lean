-- Prove2me | Theorems.Thm_FirstOrderOpt_Stochastic_stochastic_mirror_iterate_three_point
-- name    : FirstOrderOpt.Stochastic.stochastic_mirror_iterate_three_point
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:59:43.052274+00:00
-- url     : https://prove2.me/theorems/7a741c8d-494b-4977-8b4b-33f9dd95773a
-- title:
--   Lemma 3.4 (invoked for the stochastic update) — three-point inequality
-- statement:
--   The stochastic mirror-descent method minimizes $f$ over a closed convex set $X$ by the update
--   $x_{t+1} := \arg\min_{x\in X}\ \gamma_t\langle G_t,x\rangle + V(x_t,x)$ (Eq. (4.1.6)), where
--   $G_t = G(x_t,\xi_t)$ is a stochastic gradient at $x_t$ (an unbiased estimator of a true
--   subgradient $g(x_t)$) and $V$ is the Bregman divergence of a distance-generating function
--   $\nu$, exactly as in the deterministic mirror-descent update (3.2.5) of the previous chapter,
--   with $G_t$ in place of the deterministic subgradient functional $g_t$.
--
--   **Lemma 3.4** (as invoked at p. 115: "It can be easily seen that the result in Lemma 3.4 holds
--   with $g_t$ replaced by $G_t$"). For every $x \in X$,
--   $$\gamma_t\, G_t(x_{t+1}-x) + V(x_t,x_{t+1}) \le V(x_t,x) - V(x_{t+1},x).$$
--
--   This is the single algebraic fact — a property of the update's own first-order optimality
--   condition, needing nothing about $G_t$ being unbiased or having bounded variance — from which
--   the goal theorem's proof begins: replacing $g_t$ by $G_t$ in Lemma 3.4's derivation is valid
--   because the derivation never uses any property of $g_t$ beyond it being *some* continuous
--   linear functional defining the update, which $G_t$ equally is (for a fixed sample path).
--
--   **Formalization Note.** Restated in this chapter's own sub-namespace, `FirstOrderOpt.Stochastic`,
--   rather than imported from `FirstOrderOpt.Deterministic.mirror_iterate_three_point`: that item
--   is chunk `03-deterministic`'s own draft, and a draft cannot import another draft's declarations
--   (see `MODERATION_NOTES.md`). As in the original Lemma 3.4, the book's "for any $y \in X$"
--   quantifies over a letter it then does not use in the displayed inequality (which reads $x$
--   throughout) — the same erratum chunk `03-deterministic` recorded; formalized with the single
--   free variable $x \in X$ that the inequality actually has.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 60, Lemma 3.4 (invoked for the stochastic update at p. 115)

import Mathlib

namespace FirstOrderOpt.Stochastic

/-- Lemma 3.4 (three-point inequality), restated for the stochastic mirror-descent update as
invoked at p. 115: "It can be easily seen that the result in Lemma 3.4 holds with `gt` replaced
by `Gt`." `xt1` minimizes `u ↦ γt·Gt(u) + V(xt,u)` over `X` (the stochastic update (4.1.6), the
same three-point-defining minimality as (3.2.5) with the stochastic gradient functional `Gt` in
place of the deterministic subgradient `gt`); then for every `x ∈ X`,
`γt·Gt(xt1-x) + V(xt,xt1) ≤ V(xt,x) - V(xt1,x)`. As in Lemma 3.4 itself, the book quantifies over
`y ∈ X` but uses `x` in the body; read as a single free variable. Restated locally in this
sub-namespace (rather than imported from `FirstOrderOpt.Deterministic`) because chunk
`03-deterministic`'s `mirror_iterate_three_point` is itself an unpublished draft; see
`MODERATION_NOTES.md`. -/
theorem stochastic_mirror_iterate_three_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (V : E → E → ℝ) (xt xt1 : E) (Gt : E →L[ℝ] ℝ) (γt : ℝ)
    (hxt1 : xt1 ∈ X)
    (hmin : ∀ x ∈ X, γt * Gt xt1 + V xt xt1 ≤ γt * Gt x + V xt x) :
    ∀ x ∈ X, γt * Gt (xt1 - x) + V xt xt1 ≤ V xt x - V xt1 x := by sorry

end FirstOrderOpt.Stochastic
