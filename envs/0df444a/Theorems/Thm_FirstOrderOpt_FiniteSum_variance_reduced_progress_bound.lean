-- Prove2me | Theorems.Thm_FirstOrderOpt_FiniteSum_variance_reduced_progress_bound
-- name    : FirstOrderOpt.FiniteSum.variance_reduced_progress_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:01:38.710989+00:00
-- url     : https://prove2.me/theorems/e5e39b53-5600-4f66-b26b-742cd0d9f156
-- title:
--   Lemma 5.14 — one-step progress bound
-- statement:
--   The variance-reduced mirror-descent update (Algorithm 5.6) sets
--   $x_{t+1}:=\arg\min_{x\in X}\{\gamma[\langle G_t,x\rangle+h(x)]+V(x_t,x)\}$, where $V$ is the
--   Bregman divergence of a fixed distance-generating function and $\gamma$ is the (constant)
--   stepsize. Suppose $f$ is possibly $\mu$-strongly convex ($\mu\ge0$): $f(y)\ge
--   f(x)+\langle\nabla f(x),y-x\rangle+\mu V(x,y)$ for all $x,y\in X$ (Eq. (5.3.2)), and let
--   $L\ge L_f$ bound the Lipschitz constant of $\nabla f$.
--
--   **Lemma 5.14.** If the stepsize $\gamma$ satisfies $L\gamma\le 1/2$, then for any $x\in X$,
--   $$\gamma[\Psi(x_{t+1})-\Psi(x)]+V(x_{t+1},x) \le (1-\gamma\mu)V(x_t,x)+\gamma\langle\delta_t,x-x_t\rangle+\gamma^2\|\delta_t\|_*^2.$$
--
--   This is the one-step progress bound from which the chapter's epoch-level convergence result
--   (Theorem 5.6) is obtained by summing over the iterations of an epoch and taking expectation;
--   it resembles Lemma 4.2 for the original (non-variance-reduced) stochastic mirror descent
--   method, with the noise term $\delta_t$ playing the same role.
--
--   **Formalization Note.** The strong-convexity hypothesis (5.3.2) is stated directly; the lemma
--   holds for general $\mu\ge0$ (the book's §5.3.1 sets $\mu=0$, §5.3.2 takes $\mu>0$, so this
--   milestone keeps $\mu$ free, matching the book's own generality at this point). The update's
--   minimality (the composite three-point condition invoked from Lemma 3.5) is restated locally in
--   this chapter's own sub-namespace, `FirstOrderOpt.FiniteSum`, rather than imported from another
--   chunk's mirror-descent milestone, because the mirror-descent chunks of this series are
--   themselves unpublished drafts (Hard Rule 10; see `MODERATION_NOTES.md`).
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 280, Lemma 5.14

import Mathlib

namespace FirstOrderOpt.FiniteSum

/-- Lemma 5.14 (one-step progress bound, Eq. (5.3.10)). If the stepsize `γ` satisfies `Lγ ≤ 1/2`
(`L` the overall smoothness constant `Lf ≤ L := (1/m)Σ Li` of the smooth part `f`), and `xt1`
minimizes `u ↦ γ[⟨Gt,u⟩+h(u)]+V(xt,u)` over `X` (the update of Algorithm 5.6), then for any
`x ∈ X`, `γ[Ψ(xt1)-Ψ(x)] + V(xt1,x) ≤ (1-γμ)V(xt,x) + γ⟨δt,x-xt⟩ + γ²‖δt‖²_∗`, where
`δt := Gt - ∇f(xt)` and `μ ≥ 0` is `f`'s strong-convexity modulus of (5.3.2).

**Formalization Note.** `hstrong` states (5.3.2) directly (`f y ≥ f x + ⟨∇f(x),y-x⟩ + μV(x,y)`);
the lemma holds for general `μ ≥ 0` (the book's §5.3.2 specializes to `μ > 0`, §5.3.1 to `μ = 0`,
so this milestone keeps `μ` free, matching the book's own generality here). `hmin` is the
mirror-descent-with-composite-term three-point minimality (Lemma 3.5, invoked in the proof),
restated locally since the mirror-descent chunks are themselves unpublished drafts (Hard Rule
10; see `MODERATION_NOTES.md`). -/
theorem variance_reduced_progress_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (f h Ψ : E → ℝ) (hΨ : ∀ x, Ψ x = f x + h x)
    (V : E → E → ℝ)
    (gradf_full : E → E →L[ℝ] ℝ)
    (L : ℝ) (hL : 0 < L) (hsmooth : ∀ x y, ‖gradf_full x - gradf_full y‖ ≤ L * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hstrong : ∀ x y, f y ≥ f x + (gradf_full x) (y - x) + μ * V x y)
    (γ : ℝ) (hγ : 0 < γ) (hLγ : L * γ ≤ 1 / 2)
    (xt xt1 : E) (hxt : xt ∈ X) (hxt1 : xt1 ∈ X)
    (Gt δt : E →L[ℝ] ℝ) (hδt : δt = Gt - gradf_full xt)
    (hmin : ∀ y ∈ X, γ * (Gt xt1) + γ * h xt1 + V xt xt1 ≤ γ * (Gt y) + γ * h y + V xt y) :
    ∀ x ∈ X, γ * (Ψ xt1 - Ψ x) + V xt1 x ≤
      (1 - γ * μ) * V xt x + γ * (δt (x - xt)) + γ ^ 2 * ‖δt‖ ^ 2 := by sorry

end FirstOrderOpt.FiniteSum
