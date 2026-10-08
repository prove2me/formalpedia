-- Prove2me | Theorems.Thm_FenchelRobust_Counterpart_eq_7_ri_intersection
-- name    : FenchelRobust.Counterpart.eq_7_ri_intersection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T09:29:49.756873+00:00
-- url     : https://prove2.me/theorems/923286cc-dd48-468e-bd01-955e22cb2dd6
-- title:
--   Eq. (7) — relative interiors of uncertainty set and function domain meet
-- statement:
--   Let $Z\subseteq\mathbb R^L$ be convex with $0\in\operatorname{ri}Z$, let $U=a^0+AZ$, and suppose the nominal vector is regular: $a^0\in\operatorname{ri}D(x)$ for every decision $x$. Then
--   $$\operatorname{ri}U\cap\operatorname{ri}D(x)\ne\varnothing\qquad\text{for every }x\in\mathbb R^n.$$
--   This is the relative-interior qualification used for the Fenchel duality step of Theorem 2.
--
--   **Formalization Note.** The equation itself uses only convexity of $Z$, its relative-interior condition, and regularity. Compactness from the section setup is unnecessary here.
-- source:
--   Ben-Tal, den Hertog, Vial, Deriving robust counterparts of nonlinear uncertain inequalities, CentER Discussion Paper 2012-053 (July 2, 2012), p. 4, Eq. (7) and preceding paragraph

import Mathlib
import Definitions.Def_FenchelRobust_Counterpart_Model

namespace FenchelRobust.Counterpart

/-- Equation (7): the relative interiors of the uncertainty set and every effective domain meet. -/
theorem eq_7_ri_intersection {m n L : ℕ} (a0 : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin L) ℝ) (Z : Set (Fin L → ℝ))
    (D : (Fin n → ℝ) → Set (Fin m → ℝ))
    (hZconvex : Convex ℝ Z) (hZzero : (0 : Fin L → ℝ) ∈ intrinsicInterior ℝ Z)
    (hregular : Regular a0 D) :
    ∀ x : Fin n → ℝ,
      (intrinsicInterior ℝ (uncertaintySet a0 A Z) ∩
        intrinsicInterior ℝ (D x)).Nonempty := by sorry

end FenchelRobust.Counterpart
