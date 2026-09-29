-- Prove2me | Theorems.Thm_FirstOrderOpt_Deterministic_mirror_iterate_three_point
-- name    : FirstOrderOpt.Deterministic.mirror_iterate_three_point
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:57:43.255414+00:00
-- url     : https://prove2.me/theorems/3c1e7c45-30e9-49cc-b64b-d21e1c079a61
-- title:
--   Lemma 3.4 — three-point inequality for the mirror-descent update
-- statement:
--   Fix a general norm $\|\cdot\|$ on $\mathbb{R}^n$ (or, in Lean, on a normed space $E$) and a
--   Bregman divergence $V : E \times E \to \mathbb{R}$ associated to a distance-generating
--   function $\nu$ (§3.2, Eq. (3.2.2)). The mirror-descent update replaces the Euclidean
--   proximal term of (3.1.4) with $V$: $x_{t+1} := \arg\min_{x\in X}\ \gamma_t g_t(x) + V(x_t,x)$
--   (Eq. (3.2.5)), for a subgradient functional $g_t$ of $f$ at $x_t$.
--
--   **Lemma 3.4.** For every $x \in X$,
--   $$\gamma_t\, g_t(x_{t+1}-x) + V(x_t,x_{t+1}) \le V(x_t,x) - V(x_{t+1},x).$$
--
--   This generalizes `subgradient_iterate_three_point` (Lemma 3.1) from the Euclidean squared
--   distance to an arbitrary Bregman divergence, and is the fact `mirror_descent_bound` (Theorem
--   3.5) is built from exactly as `subgradient_descent_bound` (Theorem 3.1) is built from Lemma
--   3.1.
--
--   **Formalization Note.** Same erratum as Lemma 3.1: "for any $y\in X$" in the book, single
--   free variable $x$ here. $g_t$ is a continuous linear functional (`E →L[ℝ] ℝ`) rather than a
--   vector, since §3.2 works with a general norm and its dual $\|\cdot\|_*$ (a continuous linear
--   functional's operator norm *is* Mathlib's ready-made dual norm, so no separate dual-norm
--   definition is introduced). $V$ is left an entirely free function of two points: no property of
--   $V$ (nonnegativity, strong convexity) is needed for this lemma's *statement*, only for its
--   proof, so none is assumed here.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 60, Lemma 3.4

import Mathlib

namespace FirstOrderOpt.Deterministic

/-- Lemma 3.4 (three-point inequality for the mirror-descent update). Given `xt` and a
subgradient functional `gt` of `f` at `xt`, `xt1` minimizes `u ↦ γt·gt(u) + V(xt,u)` over `X`
(the update (3.2.5)); then for every `x ∈ X`, `γt·gt(xt1-x) + V(xt,xt1) ≤ V(xt,x) - V(xt1,x)`. As
in Lemma 3.1, the book quantifies over `y ∈ X` but uses `x` in the body; read as a single free
variable. `V` is pinned down to a genuine Bregman divergence (nonnegative, satisfying the
three-point/cosine identity (3.2.6) via its gradient-in-second-argument `dV`), since the
book's proof of this lemma needs both facts and neither holds for an arbitrary `V : E → E → ℝ`. -/
theorem mirror_iterate_three_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (V : E → E → ℝ) (dV : E → E → E →L[ℝ] ℝ) (xt xt1 : E) (gt : E →L[ℝ] ℝ) (γt : ℝ)
    (hxt : xt ∈ X) (hxt1 : xt1 ∈ X)
    (hVnonneg : ∀ x ∈ X, ∀ z ∈ X, 0 ≤ V x z)
    (hVthreepoint : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, V x z = V x y + (dV x y) (z - y) + V y z)
    (hmin : ∀ x ∈ X, γt * gt xt1 + V xt xt1 ≤ γt * gt x + V xt x) :
    ∀ x ∈ X, γt * gt (xt1 - x) + V xt xt1 ≤ V xt x - V xt1 x := by sorry

end FirstOrderOpt.Deterministic
