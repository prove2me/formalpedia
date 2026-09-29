-- Prove2me | Theorems.Thm_AKR2008_reducedPhoton2_singlet_unpolarized_00
-- name    : AKR2008.reducedPhoton2_singlet_unpolarized_00
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:28:32.105592+00:00
-- url     : https://prove2.me/theorems/deae2ec5-4641-4aeb-b0e3-e99feb0d6107
-- title:
--   Horizontal population of unpolarized singlet state is 1/2
-- statement:
--   Let $\mathcal H$ be a complex inner-product space (detector) and $\Phi_0 \in \mathcal H$ a unit vector ($\Vert\Phi_0\Vert = 1$). The horizontal diagonal entry of the reduced density operator of photon 2 in the unpolarized singlet state is:
--
--   $$ (\rho_2(\Psi_0))_{00} = \tfrac{1}{2}. $$
--
--   This reflects the fundamental symmetry of the singlet state under partial tracing, producing an unpolarized statistical mixture with equal populations $1/2$ along both orthogonal polarization axes.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem reducedPhoton2_singlet_unpolarized_00
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 0 0 = 1 / 2 := by sorry

end AKR2008
