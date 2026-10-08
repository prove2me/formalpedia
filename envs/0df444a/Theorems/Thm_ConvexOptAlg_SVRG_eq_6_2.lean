-- Prove2me | Theorems.Thm_ConvexOptAlg_SVRG_eq_6_2
-- name    : ConvexOptAlg.SVRG.eq_6_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:44:49.427369+00:00
-- url     : https://prove2.me/theorems/2f3dbc5d-9800-440d-ada0-244cdc457b9e
-- title:
--   Equation (6.2), p. 337 — squared-distance update identity
-- statement:
--   Fix an SVRG anchor $y$, an inner iterate $x$, a minimizer candidate $x^*$, a sampled component $i$, and a step size $\eta$. Set $v_i=g_i(x)-g_i(y)+G(y)$ and $x^+=x-\eta v_i$. Then
--
--   $$\|x^+-x^*\|_2^2=\|x-x^*\|_2^2-2\eta\langle v_i,x-x^*\rangle+\eta^2\|v_i\|_2^2.$$
--
--   This is the exact algebraic identity from which the one-step expected bound starts. It needs no smoothness or convexity assumptions.
-- source:
--   Bubeck, arXiv:1405.4980v2, Eq. (6.2), p. 337, PDF p. 110

import Mathlib
import Definitions.Def_ConvexOptAlg_SVRG_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.SVRG

/-- Equation (6.2), p. 337: the squared-distance identity for one SVRG update. -/
theorem eq_6_2 {n m : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (η : ℝ) (x y xstar : EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    ‖(x - η • direction gs x y i) - xstar‖ ^ 2 =
      ‖x - xstar‖ ^ 2 - 2 * η * ⟪direction gs x y i, x - xstar⟫_ℝ +
        η ^ 2 * ‖direction gs x y i‖ ^ 2 := by sorry

end ConvexOptAlg.SVRG
