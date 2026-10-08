-- Prove2me | Theorems.Thm_FirstOrderOpt_FiniteSum_variance_reduced_estimator_bound_v2
-- name    : FirstOrderOpt.FiniteSum.variance_reduced_estimator_bound_v2
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:16:46.921259+00:00
-- url     : https://prove2.me/theorems/f4928da0-ed80-4bc1-a3af-0a0d8f0555cb
-- title:
--   Lemma 5.13 — unbiasedness and variance of the variance-reduced estimator (corrected)
-- statement:
--   In the finite-sum setting of §5.3 ($X$ closed convex, $\Psi=f+h$ with $h$ convex, $f=\tfrac1m\sum_if_i$ with each $f_i$ convex and differentiable with $L_i$-Lipschitz gradient, $\nabla f=\tfrac1m\sum_i\nabla f_i$, $q$ a probability distribution, $L_Q=\tfrac1m\max_iL_i/q_i$), fix the current iterate $x_t\in X$ and the snapshot $\tilde x\in X$. Conditionally on them, the estimator value for index $i$, $G_i=\big(\nabla f_i(x_t)-\nabla f_i(\tilde x)\big)/(mq_i)+\nabla f(\tilde x)$, and its error $\delta_i=G_i-\nabla f(x_t)$ satisfy
--   $$\sum_iq_i\delta_i=0,\quad\sum_iq_i\|\delta_i\|_*^2\le 2L_Q\big[f(\tilde x)-f(x_t)-\langle\nabla f(x_t),\tilde x-x_t\rangle\big],\quad\sum_iq_i\|\delta_i\|_*^2\le 4L_Q\big[\Psi(x_t)-\Psi(x^*)+\Psi(\tilde x)-\Psi(x^*)\big]$$
--   ((5.3.6)–(5.3.8)), for an optimal solution $x^*$.
--
--   **Formalization Note.** The retired statement had free gradient functionals with no tie to $f_i$ and no convexity, so the inequality $\|\nabla f_i(x)-\nabla f_i(y)\|^2\le 2L_i[f_i(x)-f_i(y)-\langle\nabla f_i(y),x-y\rangle]$ that the proof uses was unavailable (disproved). The expectation over the single random index $i_t\sim Q$ is written as the finite weighted sum, as in the book's proof. In §5.3 the components $f_i$ are convex and smooth on the whole space $\mathbb R^n$ (problem (5.3.1) minimizes over $X$ functions defined everywhere), which is what the co-coercivity inequality of Lemma 5.8 needs; $h$ convex and $X$ closed convex are the standing assumptions.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 279, Lemma 5.13, with (5.3.6)-(5.3.8)

import Mathlib

namespace FirstOrderOpt.FiniteSum

/-- Lemma 5.13 (unbiasedness and variance bounds of the variance-reduced gradient estimator),
Lan p. 279. In the finite-sum setting of §5.3 — `X` closed convex, `Ψ = f + h` with `h` convex,
`f = (1/m) Σ_i fi` with each `fi` convex and differentiable with `Li`-Lipschitz gradient
`gradf i`, `∇f = (1/m) Σ_i gradf i`, `q` a probability distribution on `{1, …, m}`,
`LQ = (1/m) max_i (Li/qi)` — fix the current iterate `xt ∈ X` and snapshot `xtilde ∈ X`.
Conditionally on them, the estimator value for index `i`,
`G i := (gradf i xt - gradf i xtilde)/(m qi) + ∇f(xtilde)`, and its error `δ i := G i - ∇f(xt)`
satisfy: (5.3.6) `Σ_i qi δ i = 0`; (5.3.7) `Σ_i qi ‖δ i‖² ≤ 2 LQ [f(x̃) - f(xt) - ⟨∇f(xt), x̃ - xt⟩]`;
(5.3.8) `Σ_i qi ‖δ i‖² ≤ 4 LQ [Ψ(xt) - Ψ(x*) + Ψ(x̃) - Ψ(x*)]` for an optimal `x*`.

Corrected version: `gradf i` is the gradient of `fi` and each `fi` is convex (the retired
statement had free functionals with only a Lipschitz bound, so the gradient–function coupling the
proof uses was absent); `h` convex and `X` closed convex are the standing assumptions. -/
theorem variance_reduced_estimator_bound_v2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (hne : (Finset.univ : Finset (Fin m)).Nonempty)
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (f h Ψ : E → ℝ) (hΨ : ∀ x, Ψ x = f x + h x) (hhconv : ConvexOn ℝ X h)
    (fi : Fin m → E → ℝ) (hf : ∀ x, f x = (1 / (m : ℝ)) * ∑ i, fi i x)
    (hfi_conv : ∀ i, ConvexOn ℝ Set.univ (fi i))
    (gradf : Fin m → E → E →L[ℝ] ℝ)
    (hgrad : ∀ i x, HasFDerivAt (fi i) (gradf i x) x)
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
