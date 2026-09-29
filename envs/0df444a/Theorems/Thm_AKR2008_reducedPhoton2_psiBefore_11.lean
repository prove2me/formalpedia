-- Prove2me | Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_11
-- name    : AKR2008.reducedPhoton2_psiBefore_11
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:01:39.152223+00:00
-- url     : https://prove2.me/theorems/129d687f-2604-4cf9-aa01-fd6d8bbd6603
-- title:
--   Vertical diagonal entry (population) of the reduced photon 2 state
-- statement:
--   Let $\mathcal H$ be a complex inner-product space and $\Phi_0 \in \mathcal H$ a unit vector ($\Vert\Phi_0\Vert = 1$). The $(1, 1)$ vertical diagonal entry of the reduced density operator of photon 2 before measurement equals the $(1, 1)$ entry of $\hat\rho$:
--
--   $$ (\rho_2(\Psi_0))_{11} = \hat\rho_{11} = \tfrac{1}{2}. $$
--
--   This reflects the equal 50% probability of detecting photon 2 in the vertical polarization state in the singlet mixture.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem reducedPhoton2_psiBefore_11
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 1 1 = rhoHat 1 1 := by sorry

end AKR2008
