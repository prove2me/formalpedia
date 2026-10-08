-- Prove2me | Theorems.Thm_ConvexOptAlg_CoordDescent_theorem_6_8
-- name    : ConvexOptAlg.CoordDescent.theorem_6_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T19:09:20.345139+00:00
-- url     : https://prove2.me/theorems/a803dc0b-0202-492f-9867-12027cd56987
-- title:
--   Theorem 6.8, p. 341 — RCD(γ) on an α-strongly convex coordinate-smooth f satisfies E f(x_{t+1}) − f(x*) ≤ (1 − 1/κ_γ)^t (f(x₁) − f(x*))
-- statement:
--   Let $n\ge1$ and $\gamma\ge0$. Let $\beta_1,\dots,\beta_n>0$ and $\alpha>0$, and let $f:\mathbb R^n\to\mathbb R$ be differentiable and such that
--
--   1. $f$ is $\alpha$-strongly convex w.r.t. $\|x\|_{[1-\gamma]}=\sqrt{\sum_i\beta_i^{1-\gamma}x_i^2}$: $f(x)-f(y)\le\nabla f(x)^\top(x-y)-\frac{\alpha}{2}\|x-y\|_{[1-\gamma]}^2$ for all $x,y$;
--   2. for every $i\in[n]$ and $x\in\mathbb R^n$, $u\mapsto f(x+ue_i)$ is $\beta_i$-smooth, i.e. $|\nabla_i f(x+ue_i)-\nabla_i f(x)|\le\beta_i|u|$.
--
--   Let $x^*$ be the minimizer of $f$ and $\kappa_\gamma=\sum_{i=1}^n\beta_i^\gamma/\alpha$. Run RCD(γ) from $x_1\in\mathbb R^n$: $x_{s+1}=x_s-\frac{1}{\beta_{i_s}}\nabla_{i_s}f(x_s)e_{i_s}$ with $i_1,i_2,\dots$ drawn independently from $p_\gamma(i)=\beta_i^\gamma/\sum_j\beta_j^\gamma$. Then for every $t\ge0$,
--
--   $$\mathbb E f(x_{t+1})-f(x^*)\le\Big(1-\frac{1}{\kappa_\gamma}\Big)^t\big(f(x_1)-f(x^*)\big).$$
--
--   Random coordinate descent therefore converges linearly on strongly convex, coordinate-wise smooth functions, with a rate governed by the sum of the coordinate smoothness constants rather than the global smoothness constant; $\gamma=1$ recovers sampling proportional to $\beta_i$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and the gradient is an explicit map $g$ with `HasGradientAt f (g x) x`. The expectation over $i_1,\dots,i_t$ is the finite sum $\sum_{(i_1,\dots,i_t)}\prod_s p_\gamma(i_s)\,f(x_{t+1})$. The side conditions $n\ge1$, $\alpha>0$, $\beta_i>0$ are added (they make $p_\gamma$, $\kappa_\gamma$ and the step $1/\beta_i$ meaningful); $x^*$ is any minimizer (the book's standing assumption; uniqueness, assumed "for sake of notation", is not used). Convexity and differentiability, standing assumptions of §6.4, follow from the hypotheses. The book's $\kappa_\gamma\ge1$ is not assumed; it follows from the two hypotheses.
-- source:
--   Bubeck, arXiv:1405.4980v2, Theorem 6.8, p. 341 (setting: §6.4 preamble, p. 338; §6.4.1, p. 339)

import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs

namespace ConvexOptAlg.CoordDescent

/-- Theorem 6.8 (Bubeck, arXiv:1405.4980v2, p. 341): let `γ ≥ 0`, let `f : ℝⁿ → ℝ` be α-strongly convex
with respect to `‖·‖_[1−γ]` and such that `u ↦ f(x + u eᵢ)` is βᵢ-smooth for every `i ∈ [n]`,
`x ∈ ℝⁿ`, and let `κ_γ = Σᵢ βᵢ^γ / α`. Then RCD(γ) started at `x₁` satisfies, for every `t ≥ 0`,
`E f(x_{t+1}) − f(x*) ≤ (1 − 1/κ_γ)^t (f(x₁) − f(x*))`, the expectation being over the coordinates
`i₁, …, i_t` drawn independently from `p_γ`. Side conditions: `n ≥ 1`, `α > 0`, `βᵢ > 0`; `x*` is the
minimizer (standing assumption). -/
theorem theorem_6_8 {n : ℕ} (hn : 0 < n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : Fin n → ℝ) (γ α : ℝ)
    (hγ : 0 ≤ γ) (hβ : ∀ i, 0 < β i) (hα : 0 < α)
    (hsc : IsStronglyConvexWNorm f g β (1 - γ) α) (hsm : IsCoordSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y)
    (x₁ : EuclideanSpace ℝ (Fin n)) (t : ℕ) :
    rcdExpect β γ t (fun idx => f (rcdIter β g x₁ t idx)) - f xstar ≤
      (1 - 1 / kappa β γ α) ^ t * (f x₁ - f xstar) := by sorry

end ConvexOptAlg.CoordDescent
