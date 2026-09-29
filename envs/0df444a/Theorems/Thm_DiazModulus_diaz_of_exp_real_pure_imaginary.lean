-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_exp_real_pure_imaginary
-- name    : DiazModulus.diaz_of_exp_real_pure_imaginary
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T04:41:18.869566+00:00
-- url     : https://prove2.me/theorems/732c1e52-07af-4da5-b6a4-c49dcaf5d57b
-- title:
--   Purely imaginary argument, real exponential
-- statement:
--   **Diaz's conjecture for purely imaginary $u$ with real exponential.**
--
--   If $u \neq 0$ has $\mathrm{Re}\,u = 0$, $|u|$ algebraic, and $e^{u}$ real and $\neq 1$,
--   then $e^{u}$ is transcendental.
--
--   **Already settled by a node this mission owns.** A purely imaginary $u$ lies on an axis,
--   and `DiazModulus.diaz_on_axes_of_hermite_lindemann` covers exactly that, with its
--   hypothesis discharged from `DiazModulus.hermite_lindemann_holds`. One line.
--
--   **What the case is, concretely.** With $e^{u}$ real and $\mathrm{Re}\,u = 0$ we have
--   $|e^{u}| = e^{\mathrm{Re}\,u} = 1$, so $e^{u} = \pm 1$; excluding $1$ leaves
--   $e^{u} = -1$ and $u = i\pi(2n+1)$. This is the degenerate corner of the branch — the one
--   where $\log|\beta|$ vanishes and $|u|$ has a single term rather than two.
--
--   Four of the six hypotheses go unused: the argument needs only $u \neq 0$, $|u|$
--   algebraic and $\mathrm{Re}\,u = 0$. The rest are carried so the statement is literally a
--   case of its parent.
--
--   **Position.** One half of a split of `DiazModulus.diaz_of_exp_ne_one` on whether
--   $\mathrm{Re}\,u = 0$. That node sits under `diaz_of_exp_real_self_not_real`, under
--   `diaz_of_exp_real`, under the modulus conjecture, and every reduction in that chain is
--   already accepted, so closure propagates to the root.
--
--   Each split on this mission is on the ambient space, so every child is *strictly weaker*
--   than its parent. Weaker is not easier and no claim of the latter is made.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem diaz_of_exp_real_pure_imaginary :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im = 0 →
      u.im ≠ 0 → Complex.exp u ≠ 1 → u.re = 0 →
      Transcendental ℚ (Complex.exp u) := by sorry
end DiazModulus
