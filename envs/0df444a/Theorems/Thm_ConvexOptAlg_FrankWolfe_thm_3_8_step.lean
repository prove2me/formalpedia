-- Prove2me | Theorems.Thm_ConvexOptAlg_FrankWolfe_thm_3_8_step
-- name    : ConvexOptAlg.FrankWolfe.thm_3_8_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:22:46.764299+00:00
-- url     : https://prove2.me/theorems/de96b840-11b1-4ae0-9167-5f33d7a829ad
-- title:
--   §3.3, proof of Theorem 3.8, pp. 272–273 — one step of Frank–Wolfe: δ_{s+1} ≤ (1 − γ_s)δ_s + (β/2)γ_s²R²
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $\mathcal X\subseteq E$ nonempty, compact and convex, with diameter $R=\sup_{x,y\in\mathcal X}\|x-y\|$, and let $f:E\to\mathbb R$ be differentiable, convex on $\mathcal X$ and $\beta$-smooth with respect to $\|\cdot\|$ on $\mathcal X$ for some $\beta\ge0$. Let $x^*\in\mathcal X$ minimize $f$ over $\mathcal X$. Let $(x_t,y_t)_{t\ge1}$ be a run of conditional gradient descent on $\mathcal X$ with step sizes $\gamma_s\in[0,1]$ for all $s\ge1$, and write $\delta_s=f(x_s)-f(x^*)$. Then for every $s\ge1$,
--   $$\delta_{s+1}\le(1-\gamma_s)\,\delta_s+\frac{\beta}{2}\gamma_s^2R^2 .$$
--
--   This one-step recursion is the whole content of the analysis of Theorem 3.8; the rate then follows from a scalar induction.
--
--   **Formalization Note** $R$ is `Metric.diam X`, which is the supremum of $\|x-y\|$ over $x,y\in\mathcal X$ because $\mathcal X$ is compact (hence bounded). The step sizes are required to lie in $[0,1]$, which keeps every iterate in $\mathcal X$; the book applies the recursion only to $\gamma_s=2/(s+1)$, which satisfies this. $\beta\ge0$ is the usual reading of "β-smooth". The minimizer $x^*$ is the book's standing assumption (p. 242).
-- source:
--   Bubeck, arXiv:1405.4980v2, §3.3, proof of Theorem 3.8, pp. 272–273 (displayed chain and the δ_s recursion)

import Mathlib
import Definitions.Def_ConvexOptAlg_FrankWolfe_Defs

namespace ConvexOptAlg.FrankWolfe

/-- Bubeck, arXiv:1405.4980v2, proof of Theorem 3.8, pp. 272–273 (the displayed chain and its
rewriting): for a run of conditional gradient descent with step sizes `γ_s ∈ [0, 1]` on a convex
`f`, β-smooth in an arbitrary norm, over a compact convex `X` with minimizer `x∗`, and
`R = sup_{x,y∈X} ‖x − y‖ = diam X`, the gaps `δ_s = f(x_s) − f(x∗)` satisfy, for every `s ≥ 1`,
`δ_{s+1} ≤ (1 − γ_s) δ_s + (β/2) γ_s² R²`. -/
theorem thm_3_8_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (hXc : IsCompact X) (hXconv : Convex ℝ X)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hf : ConvexOn ℝ X f) (hsmooth : IsBetaSmoothNormOn X f f' β)
    (xstar : E) (hxstar : xstar ∈ X) (hopt : ∀ z ∈ X, f xstar ≤ f z)
    (γ : ℕ → ℝ) (hγ : ∀ s : ℕ, 1 ≤ s → γ s ∈ Set.Icc (0 : ℝ) 1)
    (x y : ℕ → E) (hrun : IsFrankWolfeRun X f' γ x y)
    (s : ℕ) (hs : 1 ≤ s) :
    f (x (s + 1)) - f xstar ≤
      (1 - γ s) * (f (x s) - f xstar) + β / 2 * γ s ^ 2 * Metric.diam X ^ 2 := by sorry

end ConvexOptAlg.FrankWolfe
