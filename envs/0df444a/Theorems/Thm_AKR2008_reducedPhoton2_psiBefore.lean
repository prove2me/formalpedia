-- Prove2me | Theorems.Thm_AKR2008_reducedPhoton2_psiBefore
-- name    : AKR2008.reducedPhoton2_psiBefore
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:29:55.483759+00:00
-- url     : https://prove2.me/theorems/88f28dc5-bfce-48b5-bcf7-d08f14d05ee3
-- title:
--   Reduced state of photon 2 before the measurement is $\hat\rho$ (Eqs. (1)→(3))
-- statement:
--   Let $\mathcal H$ be a complex inner-product space (the detector) and let $\Phi_0\in\mathcal H$ be a unit vector. Let
--   $$|\Psi_0\rangle = \tfrac{1}{\sqrt2}\bigl(|\uparrow\rangle_1|\downarrow\rangle_2 - |\downarrow\rangle_1|\uparrow\rangle_2\bigr)|\Phi_0\rangle$$
--   be the joint state (1) of the photon pair and the switched-off detector. Then the reduced density operator of photon 2, obtained by tracing out photon 1 and the detector, is
--   $$\rho_2(\Psi_0) = \tfrac12\bigl(|\uparrow\rangle_2\langle\uparrow|_2 + |\downarrow\rangle_2\langle\downarrow|_2\bigr) = \hat\rho.$$
--
--   This is the first half of the paper's claim below Eq. (2) that "this leads for both (1) and (2) to the same density operator for photon 2".
--
--   **Formalization Note** States and the reduced density matrix are those of the definition file `AKR2008_Defs`.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), https://doi.org/10.1103/PhysRevD.78.064051, p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem reducedPhoton2_psiBefore
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) = rhoHat := by
  sorry

end AKR2008
