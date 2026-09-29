-- Prove2me | Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_11_val
-- name    : AKR2008.reducedPhoton2_psiBefore_11_val
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:05:46.436524+00:00
-- url     : https://prove2.me/theorems/d28770aa-e1c6-4b4c-97dd-2e3942e4d128
-- title:
--   Value of vertical reduced photon 2 state entry is 1/2
-- statement:
--   Let $\mathcal H$ be a complex inner-product space and $\Phi_0 \in \mathcal H$ a unit vector ($\Vert\Phi_0\Vert = 1$). The vertical diagonal entry of the reduced density operator of photon 2 before measurement equals $1/2$:
--
--   $$ (\rho_2(\Psi_0))_{11} = \tfrac{1}{2}. $$
--
--   This reflects the fact that tracing out photon 1 and the detector leaves photon 2 in the vertical state $|1\rangle$ with probability $1/2$.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem reducedPhoton2_psiBefore_11_val
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 1 1 = 1 / 2 := by sorry

end AKR2008
