-- Prove2me | Theorems.Thm_ConvexOptAlg_NesterovStrong_theorem_3_18
-- name    : ConvexOptAlg.NesterovStrong.theorem_3_18
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:01:24.281806+00:00
-- url     : https://prove2.me/theorems/f659ce50-09bd-4576-bf17-35ef63e416ba
-- title:
--   Theorem 3.18, p. 290 — Nesterov's method on an α-strongly convex β-smooth f: f(y_t) − f(x*) ≤ ((α + β)/2)‖x₁ − x*‖² exp(−(t − 1)/√κ)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be $\alpha$-strongly convex and $\beta$-smooth, with $\alpha,\beta>0$ and condition number $\kappa=\beta/\alpha$, and let $x^*$ be a minimizer of $f$. Nesterov's accelerated gradient descent starts at an arbitrary point $x_1=y_1$ and iterates, for $t\ge1$,
--   $$y_{t+1}=x_t-\frac1\beta\nabla f(x_t),\qquad x_{t+1}=\Big(1+\frac{\sqrt\kappa-1}{\sqrt\kappa+1}\Big)y_{t+1}-\frac{\sqrt\kappa-1}{\sqrt\kappa+1}\,y_t .$$
--   Then for every $t\ge1$,
--   $$f(y_t)-f(x^*)\le\frac{\alpha+\beta}2\,\|x_1-x^*\|^2\exp\Big(-\frac{t-1}{\sqrt\kappa}\Big).$$
--
--   Projected gradient descent with step $1/\beta$ on the same class contracts at the rate $\exp(-t/\kappa)$ (Theorem 3.10); the accelerated method replaces $\kappa$ by $\sqrt\kappa$ in the exponent, which matches the lower bound of Theorem 3.15 for black-box first-order methods up to constants.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $\nabla f$ is a map `g` with `HasGradientAt f (g x) x` at every point (inside `IsBetaSmooth`), and $\alpha$-strong convexity is the published `StronglyConvexOn Set.univ f g α`, i.e. (3.13). The existence of $x^*$ is the book's standing assumption (p. 242). The hypotheses $\alpha>0$ and $\beta>0$ make $\kappa=\beta/\alpha$ and $1/\beta$ meaningful; $\beta>0$ (indeed $\beta\ge\alpha$) is implied by the other hypotheses when $n\ge1$. The statement holds for every run, i.e. every starting point.
-- source:
--   Bubeck, arXiv:1405.4980v2, Theorem 3.18, p. 290 (method: §3.7.1, p. 290)

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_ConvexOptAlg_NesterovStrong_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.NesterovStrong

/-- Bubeck, Theorem 3.18, p. 290: let `f : ℝⁿ → ℝ` be `α`-strongly convex and `β`-smooth
(gradient map `g`, `κ = β/α`), with minimizer `x*`. Then every run `(x, y)` of Nesterov's
accelerated gradient descent satisfies, for every `t ≥ 1`,
`f(y_t) − f(x*) ≤ ((α + β)/2)‖x₁ − x*‖² exp(−(t − 1)/√κ)`. -/
theorem theorem_3_18 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α)
    (hsm : IsBetaSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ z, f xstar ≤ f z)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovSCRun g α β x y)
    (t : ℕ) (ht : 1 ≤ t) :
    f (y t) - f xstar ≤
      (α + β) / 2 * ‖x 1 - xstar‖ ^ 2 * Real.exp (-(((t : ℝ) - 1) / Real.sqrt (kappa α β))) := by sorry

end ConvexOptAlg.NesterovStrong
