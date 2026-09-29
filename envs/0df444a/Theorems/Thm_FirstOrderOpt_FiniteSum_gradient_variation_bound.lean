-- Prove2me | Theorems.Thm_FirstOrderOpt_FiniteSum_gradient_variation_bound
-- name    : FirstOrderOpt.FiniteSum.gradient_variation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:00:50.649625+00:00
-- url     : https://prove2.me/theorems/4c8cb0d9-9a7b-4aa8-90d2-4107a498a31f
-- title:
--   Lemma 5.12 — per-component gradient-variation bound
-- statement:
--   Consider the finite-sum composite problem $\min_{x\in X}\{\Psi(x):=f(x)+h(x)\}$ (Eq.
--   (5.3.1)), where $X\subseteq E$ is a closed convex set, $f(x)=\frac{1}{m}\sum_{i=1}^m f_i(x)$
--   is the average of $m$ smooth convex component functions, each with $L_i$-Lipschitz gradient
--   $\nabla f_i$, and $h$ is a simple, possibly nondifferentiable convex function. Let
--   $Q=\{q_1,\dots,q_m\}$ be a probability distribution on $\{1,\dots,m\}$ (the sampling
--   distribution used by the variance-reduced mirror-descent method, Algorithm 5.6), and set
--   $$L_Q := \frac{1}{m}\max_{i=1,\dots,m}\frac{L_i}{q_i}.$$
--
--   **Lemma 5.12.** Let $x^*$ be an optimal solution of (5.3.1). Then for every $x\in X$,
--   $$\frac{1}{m}\sum_{i=1}^m \frac{1}{mq_i}\|\nabla f_i(x)-\nabla f_i(x^*)\|_*^2 \le 2L_Q\,[\Psi(x)-\Psi(x^*)].$$
--
--   This is the section's basic per-component consequence of $L_i$-smoothness, obtained by summing
--   the standard co-coercivity bound $\|\nabla f_i(x)-\nabla f_i(x^*)\|_*^2\le 2L_i[f_i(x)-f_i(x^*)
--   -\langle\nabla f_i(x^*),x-x^*\rangle]$ (Lemma 5.8) over $i=1,\dots,m$ weighted by $1/(mq_i)$,
--   then using the optimality of $x^*$ and the convexity of $h$. It is the fact from which the
--   variance-reduced estimator's bounded-variance property (Lemma 5.13) is derived.
--
--   **Formalization Note.** $\nabla f_i(x)$ is modeled as a continuous linear functional `gradf i
--   x : E →L[ℝ] ℝ`, matching this series' convention for gradients/subgradients; `‖·‖` on that
--   space is the dual norm $\|\cdot\|_*$. The standing smoothness hypothesis on each $\nabla f_i$
--   and the probability-distribution hypotheses on $q$ (both part of the section's setup rather
--   than restated by Lemma 5.12 itself) are included explicitly so the statement is self-contained
--   and $L_Q$ is well-defined; `hne` supplies the nonemptiness Mathlib's `Finset.sup'` needs to
--   express the $\max_i$ in $L_Q$'s definition.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 278, Lemma 5.12

import Mathlib

namespace FirstOrderOpt.FiniteSum

/-- Lemma 5.12 (per-component gradient-variation bound). `X ⊆ E` is the closed convex feasible
set of (5.3.1), `Ψ = f + h` with `f = (1/m)Σ fi` the average of `m` component functions each with
`Li`-Lipschitz gradient `gradf i` (the standing smoothness assumption preceding (5.3.3)), `q` a
probability distribution on `{1,...,m}`, and `LQ := (1/m)·maxᵢ(Li/qi)` (5.3.4). If `xstar` is an
optimal solution of (5.3.1), then for every `x ∈ X`,
`(1/m)Σᵢ (1/(m·qi))‖gradf i x - gradf i xstar‖² ≤ 2·LQ·(Ψ x - Ψ xstar)`.

**Formalization Note.** `gradf i x : E →L[ℝ] ℝ` is `∇fi(x)` as a continuous linear functional
(matching this series' convention for gradients/subgradients, e.g. chunk `03-deterministic`'s
`g t : E →L[ℝ] ℝ`); `‖·‖` on that space is the dual norm `‖·‖_∗`. The `Li`-smoothness hypothesis
`hsmooth` and the probability-distribution hypotheses on `q` are the section's standing
assumptions (the paragraph after (5.3.1) and Algorithm 5.6's `Q = {q1,…,qm}`), not restated
inline by Lemma 5.12 itself but needed to make `LQ` and the bound meaningful; `hne` supplies the
nonemptiness Mathlib's `Finset.sup'` needs for the `maxᵢ` in (5.3.4). -/
theorem gradient_variation_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (hne : (Finset.univ : Finset (Fin m)).Nonempty)
    (X : Set E) (f h Ψ : E → ℝ) (hΨ : ∀ x, Ψ x = f x + h x)
    (fi : Fin m → E → ℝ) (hf : ∀ x, f x = (1 / (m : ℝ)) * ∑ i, fi i x)
    (gradf : Fin m → E → E →L[ℝ] ℝ)
    (L : Fin m → ℝ) (hL : ∀ i, 0 < L i)
    (hsmooth : ∀ i x y, ‖gradf i x - gradf i y‖ ≤ L i * ‖x - y‖)
    (q : Fin m → ℝ) (hq_pos : ∀ i, 0 < q i) (hq_sum : ∑ i, q i = 1)
    (LQ : ℝ) (hLQ : LQ = (1 / (m : ℝ)) * Finset.univ.sup' hne (fun i => L i / q i))
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, Ψ xstar ≤ Ψ y) :
    ∀ x ∈ X, (1 / (m : ℝ)) * ∑ i, (1 / ((m : ℝ) * q i)) * ‖gradf i x - gradf i xstar‖ ^ 2 ≤
      2 * LQ * (Ψ x - Ψ xstar) := by sorry

end FirstOrderOpt.FiniteSum
