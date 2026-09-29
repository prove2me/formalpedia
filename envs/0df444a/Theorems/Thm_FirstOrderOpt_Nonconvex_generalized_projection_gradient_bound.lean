-- Prove2me | Theorems.Thm_FirstOrderOpt_Nonconvex_generalized_projection_gradient_bound
-- name    : FirstOrderOpt.Nonconvex.generalized_projection_gradient_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:02:39.812984+00:00
-- url     : https://prove2.me/theorems/5411b6e5-0e1a-4192-9ef4-fe9e68411180
-- title:
--   Lemma 6.4 — bound on the size of the generalized projected gradient
-- statement:
--   Consider the composite problem $\Psi^* := \min_{x\in X}\{\Psi(x):=f(x)+h(x)\}$ (Eq. (6.2.1)),
--   $X\subseteq\mathbb{R}^n$ closed convex, $f$ continuously differentiable (possibly nonconvex),
--   $h$ simple convex (possibly nonsmooth, e.g. $\|\cdot\|_1$ or $\equiv0$). For a
--   distance-generating function $\nu$ with modulus 1 and prox-function $V(z,x):=\nu(x)-\nu(z)-
--   \langle\nabla\nu(z),x-z\rangle$ (Eq. (6.2.5)), the **generalized projection** is
--   $$x^+ := \arg\min_{u\in X}\{\langle g,u\rangle + \tfrac1\gamma V(x,u) + h(u)\}\quad\text{(Eq.
--   (6.2.6))},\qquad P_X(x,g,\gamma) := \tfrac1\gamma(x-x^+)\quad\text{(Eq. (6.2.7))}.$$
--   When $X=\mathbb{R}^n$ and $h\equiv0$, $P_X(x,\nabla f(x),\gamma)=\nabla f(x)$: $P_X$ is a
--   generalized projected gradient (gradient mapping) of $\Psi$ at $x$.
--
--   **Lemma 6.4.** For any $x\in X$, $g\in\mathbb{R}^n$, $\gamma>0$,
--   $$\langle g, P_X(x,g,\gamma)\rangle \ge \|P_X(x,g,\gamma)\|^2 + \tfrac1\gamma\big[h(x^+)-h(x)
--   \big].$$
--
--   This is the key inequality that lets the nonconvex mirror-descent bounds (Theorem 6.5,
--   Theorem 6.6) telescope a smoothness-based descent inequality on $f$ into one on the whole
--   composite $\Psi=f+h$: the $\langle g,\cdot\rangle$ term produced by expanding $f$'s smoothness
--   is exactly matched by the left side here, turning the crude gradient step's excess into a
--   controlled, $h$-aware quantity.
--
--   **Formalization Note.** Stated over a real inner product space (Chapter 6's own $\mathbb{R}^n$
--   generality, unlike Chapter 3's dual-functional treatment — §6.2.3 explicitly restricts to "the
--   norm $\|\cdot\|$ associated with the inner product"). $x^+$'s defining property (6.2.6) is
--   taken as its pointwise minimality over $X$, matching the style used throughout this series for
--   `argmin`-defined iterates. `PXval` is introduced as its own named quantity with the defining
--   equation `PXval = (1/γ)•(x-x+)`, rather than writing `(1/γ)•(x-x+)` inline every time, purely
--   for readability; this changes nothing about the statement.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 328, Lemma 6.4

import Mathlib

namespace FirstOrderOpt.Nonconvex

open scoped RealInnerProductSpace

/-- Lemma 6.4. `xPlus` is the generalized projection (6.2.6): the minimizer over `X` of `u ↦
⟨g,u⟩ + (1/γ)V(x,u) + h(u)`. Writing `PXval := (1/γ)•(x-xPlus)` for the generalized projected
gradient `P_X(x,g,γ)` of (6.2.7), then `⟨g,PXval⟩ ≥ ‖PXval‖² + (1/γ)[h(xPlus)-h(x)]`. -/
theorem generalized_projection_gradient_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : Set E) (h : E → ℝ) (V : E → E → ℝ)
    (x xPlus g : E) (γ : ℝ) (hγ : 0 < γ) (hx : x ∈ X) (hxPlus : xPlus ∈ X)
    (hmin : ∀ u ∈ X, ⟪g, xPlus⟫ + (1 / γ) * V x xPlus + h xPlus ≤
      ⟪g, u⟫ + (1 / γ) * V x u + h u)
    (PXval : E) (hPX : PXval = (1 / γ) • (x - xPlus)) :
    ⟪g, PXval⟫ ≥ ‖PXval‖ ^ 2 + (1 / γ) * (h xPlus - h x) := by sorry

end FirstOrderOpt.Nonconvex
