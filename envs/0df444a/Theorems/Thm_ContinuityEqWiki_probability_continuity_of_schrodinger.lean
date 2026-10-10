-- Prove2me | Theorems.Thm_ContinuityEqWiki_probability_continuity_of_schrodinger
-- name    : ContinuityEqWiki.probability_continuity_of_schrodinger
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:26.035382+00:00
-- url     : https://prove2.me/theorems/60e52e3e-fc63-4a26-adfb-a50776817934
-- title:
--   Quantum probability current: $\nabla\cdot\mathbf j+\partial_t|\Psi|^2=0$ from the Schrödinger equation
-- statement:
--   Let $\hbar>0$ and $m>0$, let $U:\mathbb R\times\mathbb R^3\to\mathbb R$ be a real potential, and let $\Psi:\mathbb R\times\mathbb R^3\to\mathbb C$ be a wavefunction of class $C^2$ jointly in $(t,\mathbf r)$ that solves the time-dependent Schrödinger equation
--   $$-\frac{\hbar^2}{2m}\nabla^2\Psi+U\Psi=i\hbar\frac{\partial\Psi}{\partial t}.$$
--   With the probability density $\rho=\Psi^*\Psi=|\Psi|^2$ and the probability current
--   $$\mathbf j=\frac{\hbar}{2mi}\big[\Psi^*(\nabla\Psi)-\Psi(\nabla\Psi^*)\big],$$
--   the continuity equation holds everywhere:
--   $$\nabla\cdot\mathbf j+\frac{\partial\rho}{\partial t}=0 .$$
--
--   This expresses local conservation of probability in quantum mechanics.
-- source:
--   Wikipedia, "Continuity equation", revision oldid=1378634825, https://en.wikipedia.org/w/index.php?title=Continuity_equation&oldid=1378634825, section "Quantum mechanics", including the box "Consistency with Schrödinger equation"

import Mathlib
import Definitions.Def_ContinuityEqWiki_Defs

namespace ContinuityEqWiki

theorem probability_continuity_of_schrodinger (hbar m : ℝ) (hhbar : 0 < hbar) (hm : 0 < m)
    (U : ℝ → Space → ℝ) (Ψ : ℝ → Space → ℂ) (hΨ : ContDiff ℝ 2 (Function.uncurry Ψ))
    (hS : SchrodingerEq hbar m U Ψ) :
    ∀ t x, div (probCurrent hbar m Ψ t) x + timeDeriv (probDensity Ψ) t x = 0 := by sorry

end ContinuityEqWiki
