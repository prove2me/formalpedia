-- Prove2me | Theorems.Thm_ConvexOptAlg_SVRG_one_step_bound
-- name    : ConvexOptAlg.SVRG.one_step_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:45:24.446118+00:00
-- url     : https://prove2.me/theorems/81acbe17-c863-4cf8-8627-ead1de6aca38
-- title:
--   §6.3, p. 337 — one-step squared-distance bound
-- statement:
--   Let the components be convex with $\beta$-Lipschitz gradients, and let $x^*$ minimize their average $f$. From a fixed inner point $x$ and anchor $y$, take one SVRG update $x^+=x-\eta v_I(x,y)$ with a uniform fresh index $I$ and step size $\eta\ge0$. Then
--
--   $$\mathbb E_I\|x^+-x^*\|_2^2\le\|x-x^*\|_2^2-2\eta(1-2\beta\eta)\bigl(f(x)-f(x^*)\bigr)+4\beta\eta^2\bigl(f(y)-f(x^*)\bigr).$$
--
--   This bounds one update and is the inequality summed over the inner loop in the paper.
--
--   **Formalization Note** The nonnegative step size is implicit in the phrase “step size”; it is needed when the convexity inequality is multiplied by $-2\eta$.
-- source:
--   Bubeck, arXiv:1405.4980v2, §6.3, p. 337, PDF p. 110, unnumbered display after Eq. (6.3)

import Mathlib
import Definitions.Def_ConvexOptAlg_SVRG_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.SVRG

/-- The unnumbered one-step display after (6.3), p. 337, conditioned on
fixed `x` and anchor `y` and averaged over the single fresh sample `i`. -/
theorem one_step_bound {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (β η : ℝ) (x y xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hβ : 0 < β) (hη : 0 ≤ η)
    (hfamily : SmoothConvexFamily fs gs β)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    uniformMean (fun i : Fin m => ‖(x - η • direction gs x y i) - xstar‖ ^ 2) ≤
      ‖x - xstar‖ ^ 2 -
        2 * η * (1 - 2 * β * η) * (objective fs x - objective fs xstar) +
        4 * β * η ^ 2 * (objective fs y - objective fs xstar) := by sorry

end ConvexOptAlg.SVRG
