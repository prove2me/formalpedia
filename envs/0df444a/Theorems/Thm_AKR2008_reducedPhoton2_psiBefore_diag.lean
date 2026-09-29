-- Prove2me | Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_diag
-- name    : AKR2008.reducedPhoton2_psiBefore_diag
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T22:44:58.022461+00:00
-- url     : https://prove2.me/theorems/18b9bb4e-8149-4568-88d0-dd3970cdce21
-- title:
--   Diagonal entries (populations) of the reduced photon 2 state
-- statement:
--   Let $\mathcal H$ be a complex inner-product space and $\Phi_0 \in \mathcal H$ a unit vector ($\Vert\Phi_0\Vert = 1$). For any polarization index $j \in \{0, 1\}$, the diagonal entry of the reduced density operator of photon 2 before measurement equals the diagonal entry of $\hat\rho$:
--
--   $$ (\rho_2(\Psi_0))_{jj} = \hat\rho_{jj} = \tfrac{1}{2}. $$
--
--   This reflects the fact that both orthogonal polarization states $|\uparrow\rangle$ and $|\downarrow\rangle$ are populated with equal probability $1/2$ in the unpolarized singlet mixture.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem reducedPhoton2_psiBefore_diag
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) (j : Fin 2) :
    reducedPhoton2 (psiBefore Φ₀) j j = rhoHat j j := by sorry

end AKR2008
