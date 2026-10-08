-- Prove2me | Theorems.Thm_ConvexOptAlg_StrongGD_eq_3_6
-- name    : ConvexOptAlg.StrongGD.eq_3_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:21:17.071809+00:00
-- url     : https://prove2.me/theorems/b87fc60c-8443-4f94-a2bf-ee91e2e76419
-- title:
--   Equation (3.6), p. 269 — co-coercivity of the gradient
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex and $\beta$-smooth with gradient $g$, where $n\ge1$ and $\beta>0$. For all $x,y\in\mathbb R^n$,
--   $$\langle g(x)-g(y),x-y\rangle\ge\frac1\beta\|g(x)-g(y)\|^2.$$
--
--   This inequality controls a gradient difference by the displacement of its arguments and is reused in Lemma 3.11.
--
--   **Formalization Note** The positive dimension and $\beta>0$ make the reciprocal meaningful; the latter is implicit in the displayed fraction.
-- source:
--   Bubeck, arXiv:1405.4980v2, Eq. (3.6), p. 269

import Mathlib
import Definitions.Def_ConvexOptAlg_StrongGD_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.StrongGD

/-- Equation (3.6), p. 269: co-coercivity of the gradient of a convex smooth function. -/
theorem eq_3_6 {n : ℕ} (hn : 0 < n) (f : E n → ℝ) (g : E n → E n) (β : ℝ)
    (hβ : 0 < β) (hsm : IsBetaSmooth f g β)
    (hcvx : ConvexOn ℝ (Set.univ : Set (E n)) f) :
    ∀ x y : E n,
      (1 / β) * ‖g x - g y‖ ^ 2 ≤ ⟪g x - g y, x - y⟫_ℝ := by sorry

end ConvexOptAlg.StrongGD
