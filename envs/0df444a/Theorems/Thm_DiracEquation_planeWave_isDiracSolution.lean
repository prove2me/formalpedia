-- Prove2me | Theorems.Thm_DiracEquation_planeWave_isDiracSolution
-- name    : DiracEquation.planeWave_isDiracSolution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T20:24:50.911014+00:00
-- url     : https://prove2.me/theorems/17e00131-bd4e-4ef6-890b-32003df8e0cf
-- title:
--   Plane waves with $(p\!\!\!/+m)u=0$ solve the Dirac equation
-- statement:
--   Let $\gamma$ be complex $4\times4$ matrices, $m \in \mathbb{R}$, let $p = (p_\mu)$ be a real
--   covector and let $u \in \mathbb{C}^4$ be a polarization satisfying the **momentum-space Dirac
--   equation**
--
--   $$\bigl(p\!\!\!/ + m\bigr)u = 0, \qquad p\!\!\!/ = \gamma^\mu p_\mu .$$
--
--   Then the plane wave
--   $$\psi(x) = u\, e^{i p_\mu x^\mu}$$
--   satisfies the Dirac equation $\bigl(i\gamma^\mu\partial_\mu - m\bigr)\psi(x) = 0$ at every point
--   $x \in \mathbb{R}^4$.
--
--   This is the construction of the free solutions of the Dirac equation from solutions of a purely
--   algebraic $4\times4$ linear system, and it is the step at which the sign convention of the phase
--   determines whether the momentum-space equation carries $+m$ or $-m$. Together with the mass-shell
--   statement it accounts for the positive- and negative-frequency spectrum of the free Dirac field.
--
--   **Formalization Note.** The gamma matrices are *not* assumed to satisfy the Clifford relation: the
--   implication holds for any four matrices, because the phase convention $e^{ip_\mu x^\mu}$ turns
--   $i\gamma^\mu\partial_\mu$ into $-p\!\!\!/$ pointwise. The derivative is the Fréchet derivative
--   along the coordinate directions, and the phase is the plain sum $\sum_\mu p_\mu x^\mu$.
-- source:
--   "Dirac equation", Wikipedia, https://en.wikipedia.org/wiki/Dirac_equation, sections "Formulation - Covariant formulation" (Dirac equation, Clifford relation {gamma^mu, gamma^nu} = 2 eta^{mu nu} I_4, Dirac representation of the gamma matrices, Hamiltonian form with alpha and beta) and "Properties - Plane wave solutions" (Klein-Gordon reduction, plane waves, momentum-space Dirac equation). Section "Plane wave solutions": psi(x) = u(p) e^{i p_mu x^mu} together with the displayed momentum-space Dirac equation (p-slash + m) u(p) = 0.

import Definitions.Def_DiracEquation_fields

namespace DiracEquation

theorem planeWave_isDiracSolution (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (m : ℝ) (p : Fin 4 → ℝ)
    (u : Fin 4 → ℂ)
    (hu : (slash g fun mu => (p mu : ℂ)).mulVec u + (m : ℂ) • u = 0) :
    IsDiracSolution g m (planeWave p u) := by sorry

end DiracEquation
