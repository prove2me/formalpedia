-- Prove2me | Theorems.Thm_ConvexOptAlg_NesterovSmooth_thm_3_19_telescoped
-- name    : ConvexOptAlg.NesterovSmooth.thm_3_19_telescoped
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:56:20.462485+00:00
-- url     : https://prove2.me/theorems/d3f34c85-79f3-4b1e-8c75-c18eb6ac888c
-- title:
--   Proof of Theorem 3.19, p. 295 — summing from s = 1 to t − 1, δ_t ≤ (β/(2λ²_{t−1}))‖u₁‖²
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex and $\beta$-smooth with $\beta>0$, let $x^*$ be a minimizer of $f$, and let $(x_t),(y_t)$ be a run of Nesterov's accelerated gradient descent for the smooth case, with step sequence $(\lambda_t)$. Put $\delta_t=f(y_t)-f(x^*)$ and $u_1=\lambda_1x_1-(\lambda_1-1)y_1-x^*$. Then for every $t\ge2$,
--
--   $$\delta_t\le\frac{\beta}{2\lambda_{t-1}^2}\,\|u_1\|^2.$$
--
--   This is the bound obtained by summing the one-step inequalities for $s=1,\dots,t-1$; together with the growth $\lambda_{t-1}\ge t/2$ it gives Theorem 3.19.
--
--   **Formalization Note** $u_1$ is written out in terms of $\lambda_1$, $x_1$, $y_1$ and $x^*$, as on the page (numerically $\lambda_1=1$, so $u_1=x_1-x^*$). The range $t\ge2$ is that of the page's summation; there $\lambda_{t-1}\ge1>0$. $x^*$ a minimizer is the standing assumption; $\beta>0$ is stated.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.19, p. 295 (display after "Summing these inequalities from s = 1 to s = t − 1")

import Mathlib
import Definitions.Def_ConvexOptAlg_NesterovSmooth_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.NesterovSmooth

/-- The telescoped bound in the proof of Theorem 3.19 (Bubeck, arXiv:1405.4980v2, p. 295,
"Summing these inequalities from s = 1 to s = t − 1"): along a run of Nesterov's accelerated
gradient descent on a convex β-smooth `f` with minimizer `x*`, with
`u₁ = λ₁x₁ − (λ₁ − 1)y₁ − x*`, for every `t ≥ 2`,
`f(y_t) − f(x*) ≤ (β/(2λ_{t−1}²))‖u₁‖²`. -/
theorem thm_3_19_telescoped {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ z, f xstar ≤ f z)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovRun g β x y) (t : ℕ) (ht : 2 ≤ t) :
    f (y t) - f xstar ≤
      β / (2 * lam (t - 1) ^ 2) * ‖lam 1 • x 1 - (lam 1 - 1) • y 1 - xstar‖ ^ 2 := by sorry

end ConvexOptAlg.NesterovSmooth
