-- Prove2me | Theorems.Thm_BlackbodyRadiation_existsUnique_pos_root_maximisation_equation
-- name    : BlackbodyRadiation.existsUnique_pos_root_maximisation_equation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T18:38:05.926485+00:00
-- url     : https://prove2.me/theorems/e9394231-5d5d-4b76-9c0d-a20e8bb68c10
-- title:
--   The maximization equation $x=n(1-e^{-x})$ has a unique positive root
-- statement:
--   Setting the derivative of the Planck spectrum to zero produces, after clearing
--   denominators, the transcendental **maximization equation**
--
--   $$x \;=\; n\,\bigl(1 - e^{-x}\bigr),$$
--
--   with $n = 5$ in the wavelength parameterization and $n = 3$ in the frequency one. The
--   equation has the trivial solution $x = 0$, which is not the peak; the physically relevant
--   solution is the positive one, and the derivation is only valid if that positive solution is
--   unique.
--
--   This milestone establishes exactly that, for every real $n > 1$: there is one and only one
--   $x > 0$ with $x = n(1 - e^{-x})$. The source solves the equation in closed form using the
--   principal branch of the Lambert $W$ function, giving $x_5 = 4.965114231\ldots$ and
--   $x_3 = 2.821439372\ldots$; existence and uniqueness here are stated without reference to
--   $W$, so that they can be proved directly and used for both indices at once.
--
--   The restriction $n > 1$ is necessary rather than cosmetic: at $n = 1$ the only solution is
--   $x = 0$, and for $n \le 1$ there is no positive root.
-- source:
--   Wien's displacement law, Wikipedia, https://en.wikipedia.org/wiki/Wien%27s_displacement_law , section "Derivation from Planck's law / Parameterization by wavelength" and "Parameterization by frequency". — the maximization equations (5 - x = 5 e^{-x}, equivalently x = 5(1 - e^{-x})) for the wavelength case and (3 - x = 3 e^{-x}) for the frequency case, whose positive roots are 4.965114231744276303... and 2.821439372122078893... .

import Mathlib
import Definitions.Def_BlackbodyRadiation_planck

namespace BlackbodyRadiation
theorem existsUnique_pos_root_maximisation_equation
    (n : ℝ) (hn : 1 < n) :
    ∃! x : ℝ, 0 < x ∧ x = n * (1 - Real.exp (-x)) := by sorry
end BlackbodyRadiation
