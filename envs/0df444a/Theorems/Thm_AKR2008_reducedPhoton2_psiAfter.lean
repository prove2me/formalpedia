-- Prove2me | Theorems.Thm_AKR2008_reducedPhoton2_psiAfter
-- name    : AKR2008.reducedPhoton2_psiAfter
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:31:52.781995+00:00
-- url     : https://prove2.me/theorems/3ad14f1b-15ea-41ea-8039-802b3fd59392
-- title:
--   Reduced state of photon 2 after the measurement is $\hat\rho$ (Eqs. (2)→(3))
-- statement:
--   Let $\mathcal H$ be a complex inner-product space (the detector) and let $\Phi_\uparrow,\Phi_\downarrow\in\mathcal H$ be unit vectors (the detector states after recording horizontal, resp. vertical, polarization of photon 1). Let
--   $$|\Psi\rangle = \tfrac{1}{\sqrt2}\bigl(|\uparrow\rangle_1|\downarrow\rangle_2|\Phi_\uparrow\rangle - |\downarrow\rangle_1|\uparrow\rangle_2|\Phi_\downarrow\rangle\bigr)$$
--   be the entangled state (2) after the detector has measured photon 1. Then the reduced density operator of photon 2 is
--   $$\rho_2(\Psi) = \tfrac12\bigl(|\uparrow\rangle_2\langle\uparrow|_2 + |\downarrow\rangle_2\langle\downarrow|_2\bigr) = \hat\rho.$$
--
--   This is the second half of the paper's claim below Eq. (2).
--
--   **Formalization Note** Orthogonality of $\Phi_\uparrow$ and $\Phi_\downarrow$ is not assumed: the claimed identity does not depend on it, because the two branches are already orthogonal on photon 1.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), https://doi.org/10.1103/PhysRevD.78.064051, p. 064051-2, Sec. II, Eqs. (2) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem reducedPhoton2_psiAfter
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φup Φdown : H) (hup : ‖Φup‖ = 1) (hdown : ‖Φdown‖ = 1) :
    reducedPhoton2 (psiAfter Φup Φdown) = rhoHat := by
  sorry

end AKR2008
