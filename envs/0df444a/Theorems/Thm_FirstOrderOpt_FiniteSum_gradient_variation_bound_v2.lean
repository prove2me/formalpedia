-- Prove2me | Theorems.Thm_FirstOrderOpt_FiniteSum_gradient_variation_bound_v2
-- name    : FirstOrderOpt.FiniteSum.gradient_variation_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:16:46.213007+00:00
-- url     : https://prove2.me/theorems/23cd5ffa-5ae4-4550-8de3-8e5b37add5ca
-- title:
--   Lemma 5.12 — per-component gradient-variation bound (corrected: gradients tied to convex $f_i$)
-- statement:
--   In the finite-sum setting of §5.3, let $X$ be closed convex, $\Psi=f+h$ with $h$ convex and $f=\tfrac1m\sum_{i=1}^mf_i$, where each $f_i$ is convex and differentiable with $L_i$-Lipschitz gradient $\nabla f_i$; let $q$ be a probability distribution on $\{1,\dots,m\}$ and $L_Q=\tfrac1m\max_iL_i/q_i$ (5.3.4). If $x^*$ is an optimal solution of (5.3.1), then for every $x\in X$
--   $$\frac1m\sum_{i=1}^m\frac1{mq_i}\|\nabla f_i(x)-\nabla f_i(x^*)\|_*^2\le 2L_Q\big[\Psi(x)-\Psi(x^*)\big].$$
--
--   **Formalization Note.** The retired statement took the gradients as a free family of functionals with only a Lipschitz bound and no convexity (disproved: the Lipschitz bound alone carries no co-coercivity). The corrected statement ties $\nabla f_i$ to $f_i$ (`HasFDerivAt`) and assumes each $f_i$ convex. In §5.3 the components $f_i$ are convex and smooth on the whole space $\mathbb R^n$ (problem (5.3.1) minimizes over $X$ functions defined everywhere), which is what the co-coercivity inequality of Lemma 5.8 needs; $h$ convex and $X$ closed convex are the standing assumptions.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 278, Lemma 5.12, with (5.3.1)-(5.3.4)

import Mathlib

namespace FirstOrderOpt.FiniteSum

/-- Lemma 5.12 (per-component gradient-variation bound), Lan p. 278. In the finite-sum setting
of §5.3, `X ⊆ E` is closed convex, `Ψ = f + h` with `h` convex and `f = (1/m) Σ_i fi` the average
of `m ≥ 1` convex component functions, each differentiable with `Li`-Lipschitz gradient
`gradf i` (the standing smoothness assumption preceding (5.3.3)); `q` is a probability
distribution on `{1, …, m}` and `LQ := (1/m) max_i (Li/qi)` (5.3.4). If `xstar` is an optimal
solution of (5.3.1), then for every `x ∈ X`,
`(1/m) Σ_i (1/(m qi)) ‖gradf i x - gradf i xstar‖² ≤ 2 LQ (Ψ x - Ψ xstar)`.

Corrected version: `gradf i` is the gradient of `fi`, each `fi` is convex, `h` is convex and `X`
is closed convex — the retired statement took `gradf` as a free family of functionals with only a
Lipschitz bound, which carries no co-coercivity. The `fi` are convex and smooth on the whole space,
as in the book (problem (5.3.1) minimizes over `X` functions defined on `ℝⁿ`). -/
theorem gradient_variation_bound_v2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (hne : (Finset.univ : Finset (Fin m)).Nonempty)
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (f h Ψ : E → ℝ) (hΨ : ∀ x, Ψ x = f x + h x) (hhconv : ConvexOn ℝ X h)
    (fi : Fin m → E → ℝ) (hf : ∀ x, f x = (1 / (m : ℝ)) * ∑ i, fi i x)
    (hfi_conv : ∀ i, ConvexOn ℝ Set.univ (fi i))
    (gradf : Fin m → E → E →L[ℝ] ℝ)
    (hgrad : ∀ i x, HasFDerivAt (fi i) (gradf i x) x)
    (L : Fin m → ℝ) (hL : ∀ i, 0 < L i)
    (hsmooth : ∀ i x y, ‖gradf i x - gradf i y‖ ≤ L i * ‖x - y‖)
    (q : Fin m → ℝ) (hq_pos : ∀ i, 0 < q i) (hq_sum : ∑ i, q i = 1)
    (LQ : ℝ) (hLQ : LQ = (1 / (m : ℝ)) * Finset.univ.sup' hne (fun i => L i / q i))
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, Ψ xstar ≤ Ψ y) :
    ∀ x ∈ X, (1 / (m : ℝ)) * ∑ i, (1 / ((m : ℝ) * q i)) * ‖gradf i x - gradf i xstar‖ ^ 2 ≤
      2 * LQ * (Ψ x - Ψ xstar) := by sorry

end FirstOrderOpt.FiniteSum
