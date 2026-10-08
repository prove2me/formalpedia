-- Prove2me | Theorems.Thm_ConvexOptAlg_NesterovStrong_thm_3_18_rate
-- name    : ConvexOptAlg.NesterovStrong.thm_3_18_rate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:00:36.592319+00:00
-- url     : https://prove2.me/theorems/f16e7c8b-b977-42b6-9643-31769fbc8e07
-- title:
--   Proof of Theorem 3.18, p. 291 — f(y_t) − f(x*) ≤ ((α + β)/2)‖x₁ − x*‖²(1 − 1/√κ)^{t−1}
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be $\alpha$-strongly convex and $\beta$-smooth with $\alpha,\beta>0$, $\kappa=\beta/\alpha$, and let $x^*$ be a minimizer of $f$ on $\mathbb R^n$. Let $(x_t),(y_t)$ be a run of Nesterov's accelerated gradient descent. Then for every $t\ge1$,
--   $$f(y_t)-f(x^*)\le\frac{\alpha+\beta}2\,\|x_1-x^*\|^2\Big(1-\frac1{\sqrt\kappa}\Big)^{t-1}.$$
--
--   This is the rate obtained by combining (3.18) at $x=x^*$ with (3.19); the exponential form of Theorem 3.18 follows from $1-u\le e^{-u}$.
--
--   **Formalization Note** The existence of the minimizer $x^*$ is the book's standing assumption (p. 242). The exponent $t-1$ is a natural-number subtraction, guarded by $t\ge1$.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.18, p. 291, display after (3.19) (first and last members)

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_ConvexOptAlg_NesterovStrong_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.NesterovStrong

/-- Bubeck, proof of Theorem 3.18, p. 291, the display combining (3.18) and (3.19) (first and
last members): for a `β`-smooth, `α`-strongly convex `f` on `ℝⁿ` with minimizer `x*` and a run
`(x, y)` of Nesterov's accelerated gradient descent, for every `t ≥ 1`,
`f(y_t) − f(x*) ≤ ((α + β)/2)‖x₁ − x*‖² (1 − 1/√κ)^{t−1}`. -/
theorem thm_3_18_rate {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α)
    (hsm : IsBetaSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ z, f xstar ≤ f z)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovSCRun g α β x y)
    (t : ℕ) (ht : 1 ≤ t) :
    f (y t) - f xstar ≤
      (α + β) / 2 * ‖x 1 - xstar‖ ^ 2 * (1 - 1 / Real.sqrt (kappa α β)) ^ (t - 1) := by sorry

end ConvexOptAlg.NesterovStrong
