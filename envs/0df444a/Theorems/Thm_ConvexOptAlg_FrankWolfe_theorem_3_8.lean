-- Prove2me | Theorems.Thm_ConvexOptAlg_FrankWolfe_theorem_3_8
-- name    : ConvexOptAlg.FrankWolfe.theorem_3_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:23:08.167059+00:00
-- url     : https://prove2.me/theorems/314ee54a-c2d2-4404-843e-724cf0640b52
-- title:
--   Theorem 3.8, p. 272 — conditional gradient descent with γ_s = 2/(s + 1) satisfies f(x_t) − f(x*) ≤ 2βR²/(t + 1) in any norm
-- statement:
--   Let $E$ be a finite-dimensional real vector space with an arbitrary norm $\|\cdot\|$ and dual norm $\|g\|_*=\sup_{\|v\|\le1}g^\top v$, and let $\mathcal X\subseteq E$ be nonempty, compact and convex, with diameter
--   $$R=\sup_{x,y\in\mathcal X}\|x-y\| .$$
--   Let $f:E\to\mathbb R$ be differentiable, convex on $\mathcal X$, and $\beta$-smooth with respect to $\|\cdot\|$ on $\mathcal X$ ($\beta\ge0$), i.e. $\|\nabla f(x)-\nabla f(y)\|_*\le\beta\|x-y\|$ for $x,y\in\mathcal X$, and let $x^*\in\mathcal X$ minimize $f$ over $\mathcal X$. Run conditional gradient descent from any $x_1\in\mathcal X$ with step sizes $\gamma_s=\frac{2}{s+1}$ for $s\ge1$:
--   $$y_t\in\operatorname*{argmin}_{y\in\mathcal X}\nabla f(x_t)^\top y,\qquad x_{t+1}=(1-\gamma_t)x_t+\gamma_ty_t .$$
--   Then for every $t\ge2$,
--   $$f(x_t)-f(x^*)\le\frac{2\beta R^2}{t+1}.$$
--
--   The rate is independent of the dimension and of the norm in which smoothness is measured, and the method needs only a linear minimization oracle over $\mathcal X$ instead of a projection.
--
--   **Formalization Note** The gradient is an explicit derivative map `f'` with `HasFDerivAt f (f' x) x`, $\nabla f(x)^\top v$ is `f' x v`, and $\|\cdot\|_*$ is the operator norm on `E →L[ℝ] ℝ`. $R$ is `Metric.diam X`, which equals the supremum above because $\mathcal X$ is compact. Convexity and smoothness are assumed on $\mathcal X$ only, which is weaker than the book's global assumptions. The existence of the minimizer $x^*$ is the book's standing assumption (p. 242); $\beta\ge0$ is the usual reading of "β-smooth". Every choice of minimizer $y_t$ is allowed, and the conclusion holds for every run.
-- source:
--   Bubeck, arXiv:1405.4980v2, Theorem 3.8, p. 272

import Mathlib
import Definitions.Def_ConvexOptAlg_FrankWolfe_Defs

namespace ConvexOptAlg.FrankWolfe

/-- Bubeck, arXiv:1405.4980v2, Theorem 3.8, p. 272: let `X` be a compact convex set in a
finite-dimensional real normed space, `f` convex and β-smooth w.r.t. the norm `‖·‖` on `X`,
`x∗ ∈ X` a minimizer of `f` over `X`, `R = sup_{x,y∈X} ‖x − y‖ = diam X`, and `γ_s = 2/(s+1)` for
`s ≥ 1`. Then every run of conditional gradient descent (3.8)–(3.9) satisfies, for every `t ≥ 2`,
`f(x_t) − f(x∗) ≤ 2βR²/(t + 1)`. -/
theorem theorem_3_8 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (hXc : IsCompact X) (hXconv : Convex ℝ X)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hf : ConvexOn ℝ X f) (hsmooth : IsBetaSmoothNormOn X f f' β)
    (xstar : E) (hxstar : xstar ∈ X) (hopt : ∀ z ∈ X, f xstar ≤ f z)
    (γ : ℕ → ℝ) (hγ : ∀ s : ℕ, 1 ≤ s → γ s = 2 / ((s : ℝ) + 1))
    (x y : ℕ → E) (hrun : IsFrankWolfeRun X f' γ x y)
    (t : ℕ) (ht : 2 ≤ t) :
    f (x t) - f xstar ≤ 2 * β * Metric.diam X ^ 2 / ((t : ℝ) + 1) := by sorry

end ConvexOptAlg.FrankWolfe
