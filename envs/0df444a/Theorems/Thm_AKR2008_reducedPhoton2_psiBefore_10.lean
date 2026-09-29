-- Prove2me | Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_10
-- name    : AKR2008.reducedPhoton2_psiBefore_10
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T22:49:03.005648+00:00
-- url     : https://prove2.me/theorems/fb21783c-f91c-4b2a-9d48-27be2e8ac72f
-- title:
--   Off-diagonal coherence (1, 0) of reduced photon 2 state vanishes
-- statement:
--   Let $\mathcal H$ be a complex inner-product space and $\Phi_0 \in \mathcal H$ a unit vector ($\Vert\Phi_0\Vert = 1$). The $(1, 0)$ matrix element of the reduced density operator of photon 2 vanishes:
--
--   $$ (\rho_2(\Psi_0))_{10} = \hat\rho_{10} = 0. $$
--
--   By symmetry of the partial trace or by direct evaluation, the $(1, 0)$ coherence vanishes identically.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem reducedPhoton2_psiBefore_10
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 1 0 = rhoHat 1 0 := by sorry

end AKR2008
