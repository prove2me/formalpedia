-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_exp_real_self_real
-- name    : DiazModulus.diaz_of_exp_real_self_real
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T04:08:05.988443+00:00
-- url     : https://prove2.me/theorems/47bdb16f-f90d-402d-958e-1a8728572240
-- title:
--   Real exponential, real argument
-- statement:
--   **Diaz's conjecture when $e^{u}$ is real and $u$ is real.**
--
--   If $u \neq 0$ is real, $|u|$ is algebraic, and $e^{u}$ is real, then $e^{u}$ is
--   transcendental.
--
--   **This half is not hard, and that is the point of separating it.** A real $u$ with $|u|$
--   algebraic is itself algebraic, since $u = \pm|u|$. Hermite–Lindemann then makes $e^{u}$
--   transcendental. On this mission both ingredients are already proved:
--   `DiazModulus.diaz_on_axes_of_hermite_lindemann` and
--   `DiazModulus.hermite_lindemann_holds`, and the second is discharged into the first.
--
--   **The hypothesis $\mathrm{Im}\,e^{u} = 0$ is redundant here.** It is carried only so
--   that this statement is literally a case of its parent; the argument never uses it. A
--   reader should not infer that the real-exponential condition does any work in this half.
--
--   Separating it is worthwhile because it removes an already-settled region from the
--   search, leaving the sibling as the actual content.
--
--   **Position.** This is one half of a split of `DiazModulus.diaz_of_exp_real` on whether
--   $u$ itself is real. That node is in turn one half of a split of the modulus conjecture
--   on whether $e^{u}$ is real, and the reduction to the conjecture is already accepted, so
--   closing this and its sibling closes `diaz_of_exp_real`, and closing that and *its*
--   sibling closes the conjecture.
--
--   Each split is on the ambient space, so every child is *strictly weaker* than its parent
--   rather than a restatement of it.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem diaz_of_exp_real_self_real :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im = 0 →
      u.im = 0 → Transcendental ℚ (Complex.exp u) := by sorry
end DiazModulus
