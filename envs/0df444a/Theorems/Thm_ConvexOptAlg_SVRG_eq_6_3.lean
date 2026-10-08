-- Prove2me | Theorems.Thm_ConvexOptAlg_SVRG_eq_6_3
-- name    : ConvexOptAlg.SVRG.eq_6_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:45:10.647005+00:00
-- url     : https://prove2.me/theorems/ae6d8127-596e-4816-bd12-59fb042f938e
-- title:
--   Equation (6.3), p. 337 — SVRG direction second moment
-- statement:
--   Under the hypotheses of Lemma 6.4, fix an inner point $x$, an anchor $y$, and a minimizer $x^*$ of $f$. For a uniform component $I\in[m]$, write $v_I(x,y)=g_I(x)-g_I(y)+G(y)$. Then
--
--   $$\mathbb E_I\|v_I(x,y)\|_2^2\le4\beta\bigl(f(x)-f(x^*)+f(y)-f(x^*)\bigr).$$
--
--   The direction's second moment is controlled by the gaps at both the current point and the anchor. This is the variance-reduction estimate used in the epoch proof.
--
--   **Formalization Note** The expectation here is over the one fresh index while $x$ and $y$ are fixed.
-- source:
--   Bubeck, arXiv:1405.4980v2, Eq. (6.3), p. 337, PDF p. 110

import Mathlib
import Definitions.Def_ConvexOptAlg_SVRG_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.SVRG

/-- Equation (6.3), p. 337: the second moment of the SVRG direction. -/
theorem eq_6_3 {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (β : ℝ) (x y xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hβ : 0 < β) (hfamily : SmoothConvexFamily fs gs β)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    uniformMean (fun i : Fin m => ‖direction gs x y i‖ ^ 2) ≤
      4 * β * (objective fs x - objective fs xstar +
        objective fs y - objective fs xstar) := by sorry

end ConvexOptAlg.SVRG
