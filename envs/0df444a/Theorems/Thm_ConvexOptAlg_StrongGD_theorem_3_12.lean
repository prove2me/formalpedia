-- Prove2me | Theorems.Thm_ConvexOptAlg_StrongGD_theorem_3_12
-- name    : ConvexOptAlg.StrongGD.theorem_3_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:22:05.42199+00:00
-- url     : https://prove2.me/theorems/614c2548-63f5-4cec-b5d7-13ca8be15ba5
-- title:
--   Theorem 3.12, p. 279 — fixed-step gradient descent on a strongly convex smooth function
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be $\alpha$-strongly convex and $\beta$-smooth with gradient $g$, where $n\ge1$ and $\alpha>0$. Let $x^*$ be a global minimizer, put $\kappa=\beta/\alpha$, and let gradient descent start at $x_1$ with step size $\eta=2/(\alpha+\beta)$. For every integer $t\ge0$,
--   $$f(x_{t+1})-f(x^*)\le\frac\beta2\exp\!\left(-\frac{4t}{\kappa+1}\right)\|x_1-x^*\|^2.$$
--
--   This gives an exponential function-value rate for a fixed step size determined by the curvature and smoothness parameters.
--
--   **Formalization Note** The book assumes a minimizer exists in its standing notation. Positive dimension excludes the degenerate zero-dimensional space; $\alpha>0$ makes the condition number meaningful. The gradient in the recursion is tied to $f$ by the smoothness predicate.
-- source:
--   Bubeck, arXiv:1405.4980v2, Theorem 3.12, p. 279

import Mathlib
import Definitions.Def_ConvexOptAlg_StrongGD_Defs
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn

open scoped InnerProductSpace

namespace ConvexOptAlg.StrongGD

/-- Theorem 3.12, p. 279: the exponential value bound for fixed-step gradient descent. -/
theorem theorem_3_12 {n : ℕ} (hn : 0 < n) (f : E n → ℝ)
    (g : E n → E n) (α β : ℝ) (hα : 0 < α)
    (hsm : IsBetaSmooth f g β)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α)
    (xstar : E n) (hstar : IsMinOn f Set.univ xstar)
    (x : ℕ → E n) (hrun : IsGDRun g (2 / (α + β)) x) :
    ∀ t : ℕ,
      f (x (t + 1)) - f xstar ≤
        (β / 2) * Real.exp (-(4 * (t : ℝ) / (β / α + 1))) * ‖x 1 - xstar‖ ^ 2 := by sorry

end ConvexOptAlg.StrongGD
