-- Prove2me | Theorems.Thm_BregmanPPA_ProxMult_saddle_iff_zero
-- name    : BregmanPPA.ProxMult.saddle_iff_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:07.906856+00:00
-- url     : https://prove2.me/theorems/3c3b7368-098a-4d12-96c5-79d005335fd3
-- title:
--   §5, p. 220 — (x*, p*) is a saddle point of l iff (0, 0) ∈ K(x*, p*)
-- statement:
--   For a problem of the form (10) with Lagrangian $l$ and saddle operator $K$, and any $(x^*,p^*)\in\mathbb R^n\times\mathbb R^m$,
--
--   $$l(x^*,p)\le l(x^*,p^*)\le l(x,p^*)\quad\forall x\in\mathbb R^n,\ p\in\mathbb R^m\qquad\Longleftrightarrow\qquad(0,0)\in K(x^*,p^*).$$
--
--   The zeros of $K$ are therefore exactly the saddle pairs, which the paper identifies with the optimal solution–Lagrange multiplier pairs of (10). This translates the conclusion of Theorem 1 for $K$ into the conclusion of Theorem 8.
--
--   **Formalization Note** The page states two equivalences: "$x^*$ optimal and $p^*$ a Lagrange multiplier" iff the saddle inequality, iff $(0,0)\in K(x^*,p^*)$. This item states the second. The first is how the paper names saddle pairs; the mission takes the saddle inequality itself as the meaning of "optimal solution–Lagrange multiplier pair".
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 220, §5 (saddle inequality ⇔ (0,0) ∈ K(x*, p*))

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_IneqMult_Program
import Definitions.Def_BregmanPPA_ProxMult_Saddle

open ThreeOpSplitting.Convergence

namespace BregmanPPA.ProxMult

/-- §5, p. 220: `(x*, p*)` satisfies the saddle inequality
`l(x*, p) ≤ l(x*, p*) ≤ l(x, p*)` for all `x, p` if and only if `(0, 0) ∈ K(x*, p*)`. -/
theorem saddle_iff_zero {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (hP : BregmanPPA.IneqMult.IsConvexProgram C f g) (x' : BregmanPPA.IneqMult.E n) (p' : BregmanPPA.IneqMult.E m) :
    IsSaddlePair C f g x' p' ↔ pair x' p' ∈ zer (opK C f g) := by sorry

end BregmanPPA.ProxMult
