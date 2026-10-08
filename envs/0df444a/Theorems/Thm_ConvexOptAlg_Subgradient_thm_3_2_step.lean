-- Prove2me | Theorems.Thm_ConvexOptAlg_Subgradient_thm_3_2_step
-- name    : ConvexOptAlg.Subgradient.thm_3_2_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:40:34.64847+00:00
-- url     : https://prove2.me/theorems/2b8a9530-adb9-4d7c-8920-05e206db4b31
-- title:
--   §3.1, proof of Theorem 3.2, p. 265 — f(x_s) − f(x*) ≤ (‖x_s − x*‖² − ‖y_{s+1} − x*‖²)/(2η) + (η/2)‖g_s‖²
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^n$ and $f:\mathbb R^n\to\mathbb R$, and let $(x_s),(g_s)$ be a run of projected subgradient descent on $f$ over $\mathcal X$ with step sizes $(\eta_s)$ for the steps $1,\dots,T$. Let $x^*\in\mathcal X$, let $1\le s\le T$ with $\eta=\eta_s>0$, and put $y_{s+1}=x_s-\eta g_s$. Then
--   $$f(x_s)-f(x^*)\le\frac{1}{2\eta}\Big(\|x_s-x^*\|^2-\|y_{s+1}-x^*\|^2\Big)+\frac{\eta}{2}\|g_s\|^2 .$$
--
--   This is the one-step inequality from which the rate of Theorem 3.2 is obtained by summation.
--
--   **Formalization Note** The page states the inequality for a constant step $\eta$; it is stated here for the step $\eta_s$ used at step $s$, which contains the constant case. Only $x^*\in\mathcal X$ is needed, not that $x^*$ is a minimizer. The positivity $\eta>0$ is the page's standing condition on a step size.
-- source:
--   Bubeck, arXiv:1405.4980v2, §3.1, proof of Theorem 3.2, p. 265, first display (first and last members)

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
import Definitions.Def_ConvexOptAlg_Subgradient_Defs

namespace ConvexOptAlg.Subgradient

/-- Bubeck, proof of Theorem 3.2, p. 265, first display (first and last members): for a run of
projected subgradient descent and a step `1 ≤ s ≤ T` with `η s > 0`, writing
`y_{s+1} = x s - η s • g s`,
`f(x_s) - f(x*) ≤ (1/(2η))(‖x_s - x*‖² - ‖y_{s+1} - x*‖²) + (η/2)‖g_s‖²`. -/
theorem thm_3_2_step {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (η : ℕ → ℝ) (x g : ℕ → EuclideanSpace ℝ (Fin n))
    (T : ℕ) (hrun : IsProjSubgradRun X f η x g T) (xstar : EuclideanSpace ℝ (Fin n))
    (hxstar : xstar ∈ X) (s : ℕ) (hs1 : 1 ≤ s) (hsT : s ≤ T) (hη : 0 < η s) :
    f (x s) - f xstar ≤
      1 / (2 * η s) * (‖x s - xstar‖ ^ 2 - ‖(x s - η s • g s) - xstar‖ ^ 2)
        + η s / 2 * ‖g s‖ ^ 2 := by sorry

end ConvexOptAlg.Subgradient
