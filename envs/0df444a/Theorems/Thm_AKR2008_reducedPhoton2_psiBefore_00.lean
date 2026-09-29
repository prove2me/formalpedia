-- Prove2me | Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_00
-- name    : AKR2008.reducedPhoton2_psiBefore_00
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:01:44.702476+00:00
-- url     : https://prove2.me/theorems/b4f8e127-e320-40fe-838f-da531ef2b606
-- title:
--   Horizontal diagonal entry (population) of the reduced photon 2 state
-- statement:
--   Let $\mathcal H$ be a complex inner-product space and $\Phi_0 \in \mathcal H$ a unit vector ($\Vert\Phi_0\Vert = 1$). The $(0, 0)$ horizontal diagonal entry of the reduced density operator of photon 2 before measurement equals the $(0, 0)$ entry of $\hat\rho$:
--
--   $$ (\rho_2(\Psi_0))_{00} = \hat\rho_{00} = \tfrac{1}{2}. $$
--
--   This reflects the equal 50% probability of detecting photon 2 in the horizontal polarization state in the singlet mixture.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem reducedPhoton2_psiBefore_00
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 0 0 = rhoHat 0 0 := by sorry

end AKR2008
