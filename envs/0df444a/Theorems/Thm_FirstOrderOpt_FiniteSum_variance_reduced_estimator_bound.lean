-- Prove2me | Theorems.Thm_FirstOrderOpt_FiniteSum_variance_reduced_estimator_bound
-- name    : FirstOrderOpt.FiniteSum.variance_reduced_estimator_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:01:18.361981+00:00
-- url     : https://prove2.me/theorems/d64513f6-1d80-4d2b-97a9-8a68865e8906
-- title:
--   Lemma 5.13 — unbiasedness and variance bound of the variance-reduced gradient estimator
-- statement:
--   At iteration $t$ of an epoch with current iterate $x_t$ and snapshot point $\tilde x$
--   (Algorithm 5.6 recomputes $\tilde g=\nabla f(\tilde x)$ once per epoch), a random index
--   $i_t\in\{1,\dots,m\}$ is drawn from $Q=\{q_1,\dots,q_m\}$ and the gradient estimator
--   $$G_t := \frac{\nabla f_{i_t}(x_t)-\nabla f_{i_t}(\tilde x)}{q_{i_t}\,m} + \tilde g$$
--   is formed; write $\delta_t := G_t-\nabla f(x_t)$ for its error.
--
--   **Lemma 5.13.** Conditionally on $x_1,\dots,x_t$ (i.e. treating $x_t,\tilde x$ as fixed and
--   taking expectation over the draw of $i_t$ only),
--   $$\mathbb E[\delta_t]=0,\qquad
--   \mathbb E[\|\delta_t\|_*^2]\le 2L_Q\big[f(\tilde x)-f(x_t)-\langle\nabla f(x_t),\tilde x-x_t\rangle\big],\qquad
--   \mathbb E[\|\delta_t\|_*^2]\le 4L_Q\big[\Psi(x_t)-\Psi(x^*)+\Psi(\tilde x)-\Psi(x^*)\big].$$
--
--   This shows $G_t$ is an unbiased estimator of $\nabla f(x_t)$ whose variance shrinks to zero as
--   both $x_t$ and $\tilde x$ approach the optimum $x^*$ — the defining property that distinguishes
--   variance-reduced mirror descent from the basic scheme, which uses $\nabla f_{i_t}(x_t)$
--   directly and whose variance stays bounded away from zero throughout.
--
--   **Formalization Note.** "Conditionally on $x_1,\dots,x_t$" is modeled as a finite expectation
--   $\sum_i q_i\cdot(\cdot)$ over the single random draw $i_t\sim Q$ (rather than a full
--   filtration), since $x_t$ and $\tilde x$ are already-fixed points at this stage and the only
--   remaining randomness is $i_t$'s own draw — the per-index value `G i` is the value $G_t$ takes
--   when $i_t=i$, and `δ i := G i - ∇f(x_t)`. `∇f`, tied to the component gradients by the average
--   identity $\nabla f=\frac1m\sum_i\nabla f_i$, is a separate functional `gradf_full`. The three
--   displayed equations of Lemma 5.13 are conjoined into one conclusion, as in the book's single
--   lemma.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 279, Lemma 5.13

import Mathlib

namespace FirstOrderOpt.FiniteSum

/-- Lemma 5.13 (unbiasedness and variance bounds of the variance-reduced gradient estimator).
Conditionally on the current iterate `xt` and snapshot `xtilde` (i.e. treating them as fixed and
taking expectation only over the random index `it` drawn from `Q = {q1,…,qm}`, as in Algorithm
5.6), the per-index estimator value `G i := (gradf i xt - gradf i xtilde)/(m·qi) + gradf_full
xtilde` (the value `Gt` takes when `it = i`) and its error `δ i := G i - gradf_full xt` satisfy:
`(5.3.6)` the weighted-average error is zero, `(5.3.7)` its weighted second moment is bounded by
`2·LQ` times the gap `f(x̃) - f(xt) - ⟨∇f(xt), x̃-xt⟩`, and `(5.3.8)` by `4·LQ` times the sum of
objective gaps at `xt` and `x̃`.

**Formalization Note.** "Conditionally on `x1,…,xt`" is modeled as a finite expectation
`Σᵢ qᵢ • (·)` over the single random draw `it ~ Q`, rather than a full filtration, since `xt` and
`x̃` are already-fixed points at this stage of the algorithm and the only remaining randomness is
`it`'s own draw — matching how Lemma 5.12's proof (5.3.5) itself sums over `i = 1,…,m` weighted by
`1/(mqi)`. `gradf_full x : E →L[ℝ] ℝ` is `∇f(x)`, tied to the component gradients by `hgradf_avg`
(the average matching `f = (1/m)Σfi`, differentiated). The three conclusions of Lemma 5.13 are
conjoined, as in the book's single lemma with three displayed equations. -/
theorem variance_reduced_estimator_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (hne : (Finset.univ : Finset (Fin m)).Nonempty)
    (X : Set E) (f h Ψ : E → ℝ) (hΨ : ∀ x, Ψ x = f x + h x)
    (fi : Fin m → E → ℝ) (hf : ∀ x, f x = (1 / (m : ℝ)) * ∑ i, fi i x)
    (gradf : Fin m → E → E →L[ℝ] ℝ)
    (gradf_full : E → E →L[ℝ] ℝ)
    (hgradf_avg : ∀ x, gradf_full x = (1 / (m : ℝ)) • ∑ i, gradf i x)
    (L : Fin m → ℝ) (hL : ∀ i, 0 < L i)
    (hsmooth : ∀ i x y, ‖gradf i x - gradf i y‖ ≤ L i * ‖x - y‖)
    (q : Fin m → ℝ) (hq_pos : ∀ i, 0 < q i) (hq_sum : ∑ i, q i = 1)
    (LQ : ℝ) (hLQ : LQ = (1 / (m : ℝ)) * Finset.univ.sup' hne (fun i => L i / q i))
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, Ψ xstar ≤ Ψ y)
    (xt xtilde : E) (hxt : xt ∈ X) (hxtilde : xtilde ∈ X)
    (G : Fin m → E →L[ℝ] ℝ)
    (hG : ∀ i, G i = (1 / (q i * (m : ℝ))) • (gradf i xt - gradf i xtilde) + gradf_full xtilde)
    (δ : Fin m → E →L[ℝ] ℝ) (hδ : ∀ i, δ i = G i - gradf_full xt) :
    (∑ i, q i • δ i = 0) ∧
    (∑ i, q i * ‖δ i‖ ^ 2 ≤ 2 * LQ * (f xtilde - f xt - (gradf_full xt) (xtilde - xt))) ∧
    (∑ i, q i * ‖δ i‖ ^ 2 ≤ 4 * LQ * (Ψ xt - Ψ xstar + Ψ xtilde - Ψ xstar)) := by sorry

end FirstOrderOpt.FiniteSum
