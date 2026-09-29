-- Prove2me | Theorems.Thm_DiracEquation_slash_sq
-- name    : DiracEquation.slash_sq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T20:18:49.305047+00:00
-- url     : https://prove2.me/theorems/bbb0e2a4-8f4f-45a7-a247-6ae5fb7c19dd
-- title:
--   $p\!\!\!/\,p\!\!\!/ = (\eta^{\mu\nu}p_\mu p_\nu)\,I_4$
-- statement:
--   Let $\gamma$ be any family of complex $4\times4$ matrices satisfying the Clifford relation
--   $\gamma^\mu\gamma^\nu + \gamma^\nu\gamma^\mu = 2\eta^{\mu\nu}I_4$ for
--   $\eta = \operatorname{diag}(1,-1,-1,-1)$, and let $p = (p_\mu)$ be a covector with complex
--   entries. Writing $p\!\!\!/ = \gamma^\mu p_\mu$ for the Feynman slash, one has
--
--   $$p\!\!\!/\;p\!\!\!/ \;=\; \bigl(\eta^{\mu\nu} p_\mu p_\nu\bigr)\, I_4
--   \;=\; \bigl(p_0^2 - p_1^2 - p_2^2 - p_3^2\bigr)\, I_4 .$$
--
--   This identity is the algebraic heart of the Dirac theory: the first-order operator $p\!\!\!/$ is a
--   square root of the quadratic form of Minkowski space. It is the momentum-space counterpart of the
--   Klein--Gordon reduction, and it is what forces a nonzero solution of the momentum-space Dirac
--   equation onto the mass shell.
--
--   **Formalization Note.** The identity holds for every family satisfying the Clifford relation, in
--   any representation, and the components of $p$ are allowed to be arbitrary complex numbers rather
--   than real momenta.
-- source:
--   "Dirac equation", Wikipedia, https://en.wikipedia.org/wiki/Dirac_equation, sections "Formulation - Covariant formulation" (Dirac equation, Clifford relation {gamma^mu, gamma^nu} = 2 eta^{mu nu} I_4, Dirac representation of the gamma matrices, Hamiltonian form with alpha and beta) and "Properties - Plane wave solutions" (Klein-Gordon reduction, plane waves, momentum-space Dirac equation). Section "Plane wave solutions": the Klein-Gordon reduction (i d-slash + m)(i d-slash - m) psi = (d_mu d^mu + m^2) psi, of which this is the momentum-space form.

import Definitions.Def_DiracEquation_fields

namespace DiracEquation

theorem slash_sq (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (hg : IsGammaFamily g) (p : Fin 4 → ℂ) :
    slash g p * slash g p = (∑ mu, eta mu mu * p mu * p mu) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  sorry

end DiracEquation
