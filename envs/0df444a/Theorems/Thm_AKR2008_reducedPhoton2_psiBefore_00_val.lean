-- Prove2me | Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_00_val
-- name    : AKR2008.reducedPhoton2_psiBefore_00_val
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:05:06.248741+00:00
-- url     : https://prove2.me/theorems/a86a34d8-fc6e-460c-80e5-64438e5dff53
-- title:
--   Value of horizontal reduced photon 2 state entry is 1/2
-- statement:
--   Let $\mathcal H$ be a complex inner-product space and $\Phi_0 \in \mathcal H$ a unit vector ($\Vert\Phi_0\Vert = 1$). The horizontal diagonal entry of the reduced density operator of photon 2 before measurement equals $1/2$:
--
--   $$ (\rho_2(\Psi_0))_{00} = \tfrac{1}{2}. $$
--
--   This reflects the fact that tracing out photon 1 and the detector leaves photon 2 in the horizontal state $|0\rangle$ with probability $1/2$.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem reducedPhoton2_psiBefore_00_val
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 0 0 = 1 / 2 := by sorry

end AKR2008
