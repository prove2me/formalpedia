-- Prove2me | Theorems.Thm_ConvexOptAlg_FrankWolfe_thm_3_8_init
-- name    : ConvexOptAlg.FrankWolfe.thm_3_8_init
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:22:51.340486+00:00
-- url     : https://prove2.me/theorems/ee3c2a1d-dc26-4ce7-aeb0-4d4736474780
-- title:
--   §3.3, proof of Theorem 3.8, p. 273 — initialization: with γ₁ = 1, δ₂ ≤ (β/2)R²
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $\mathcal X\subseteq E$ nonempty, compact and convex, with diameter $R=\sup_{x,y\in\mathcal X}\|x-y\|$, and let $f:E\to\mathbb R$ be differentiable, convex on $\mathcal X$ and $\beta$-smooth with respect to $\|\cdot\|$ on $\mathcal X$ for some $\beta\ge0$. Let $x^*\in\mathcal X$ minimize $f$ over $\mathcal X$, and let $(x_t,y_t)_{t\ge1}$ be a run of conditional gradient descent on $\mathcal X$ whose first step size is $\gamma_1=1$. Then
--   $$f(x_2)-f(x^*)\le\frac{\beta}{2}R^2 .$$
--
--   With $\gamma_s=2/(s+1)$ one has $\gamma_1=1$, so this is the base case of the induction that proves Theorem 3.8, whatever the starting point $x_1\in\mathcal X$.
--
--   **Formalization Note** Only $\gamma_1$ is constrained; the later step sizes play no role. $R$ is `Metric.diam X` ($\mathcal X$ compact). $\beta\ge0$ and the existence of $x^*$ are as in the book (standing assumption, p. 242).
-- source:
--   Bubeck, arXiv:1405.4980v2, §3.3, proof of Theorem 3.8, p. 273 ("the initialization is done at step 2 with the above inequality yielding δ₂ ≤ (β/2)R²")

import Mathlib
import Definitions.Def_ConvexOptAlg_FrankWolfe_Defs

namespace ConvexOptAlg.FrankWolfe

/-- Bubeck, arXiv:1405.4980v2, proof of Theorem 3.8, p. 273 ("the initialization is done at step 2
with the above inequality yielding δ₂ ≤ (β/2)R²"): for a run of conditional gradient descent with
`γ₁ = 1` on a convex `f`, β-smooth in an arbitrary norm, over a compact convex `X` with minimizer
`x∗`, and `R = diam X`, one has `f(x₂) − f(x∗) ≤ (β/2) R²`. -/
theorem thm_3_8_init {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (hXc : IsCompact X) (hXconv : Convex ℝ X)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hf : ConvexOn ℝ X f) (hsmooth : IsBetaSmoothNormOn X f f' β)
    (xstar : E) (hxstar : xstar ∈ X) (hopt : ∀ z ∈ X, f xstar ≤ f z)
    (γ : ℕ → ℝ) (hγ1 : γ 1 = 1)
    (x y : ℕ → E) (hrun : IsFrankWolfeRun X f' γ x y) :
    f (x 2) - f xstar ≤ β / 2 * Metric.diam X ^ 2 := by sorry

end ConvexOptAlg.FrankWolfe
