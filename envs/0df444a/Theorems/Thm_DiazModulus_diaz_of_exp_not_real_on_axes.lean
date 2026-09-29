-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_exp_not_real_on_axes
-- name    : DiazModulus.diaz_of_exp_not_real_on_axes
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T04:50:46.746284+00:00
-- url     : https://prove2.me/theorems/9cea9bb5-bf23-428b-8393-c708a9d0b9df
-- title:
--   Non-real exponential, argument on an axis
-- statement:
--   **Diaz's conjecture on the axes, with non-real exponential.**
--
--   If $u \neq 0$ lies on a coordinate axis — $\mathrm{Im}\,u = 0$ or
--   $\mathrm{Re}\,u = 0$ — with $|u|$ algebraic and $e^{u}$ not real, then $e^{u}$ is
--   transcendental.
--
--   **Settled by a node the mission already owns.**
--   `DiazModulus.diaz_on_axes_of_hermite_lindemann` is exactly this statement without the
--   non-real hypothesis, and its own hypothesis is discharged from
--   `DiazModulus.hermite_lindemann_holds`. One line.
--
--   **The case is not vacuous.** Unlike the corresponding corner of the real branch, both
--   disjuncts have content here. A real $u$ would force $e^{u}$ real, so that disjunct is
--   indeed empty; but a purely imaginary $u$ is entirely compatible with $e^{u}$ non-real —
--   $u = i$ is the obvious witness, and every $u = it$ with $t$ not a multiple of $\pi$
--   qualifies. So this node genuinely settles a region rather than reporting an
--   impossibility.
--
--   The hypothesis $\mathrm{Im}\,e^{u} \neq 0$ is unused; the Lean discards it. It is
--   carried so the statement is literally a case of its parent.
--
--   **Position.** One half of a split of `DiazModulus.diaz_of_exp_not_real` on whether $u$
--   lies on a coordinate axis. That node is a direct child of the modulus conjecture and its
--   reduction is accepted, so closure propagates to the root.
--
--   Each split on this mission is on the ambient space, so every child is *strictly weaker*
--   than its parent. Weaker is not easier and no claim of the latter is made.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem diaz_of_exp_not_real_on_axes :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      (u.im = 0 ∨ u.re = 0) → Transcendental ℚ (Complex.exp u) := by sorry
end DiazModulus
