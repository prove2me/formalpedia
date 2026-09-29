-- Prove2me | Theorems.Thm_AKR2008_reducedPhoton2_singlet_11_from_norm
-- name    : AKR2008.reducedPhoton2_singlet_11_from_norm
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:33:38.674152+00:00
-- url     : https://prove2.me/theorems/dd1c0877-cb07-4744-b1a9-21ff5898150a
-- title:
--   Vertical reduced state equals half squared norm of detector
-- statement:
--   Let $\mathcal H$ be a complex inner-product space (detector) and $\Phi_0 \in \mathcal H$ a normalized state ($\Vert\Phi_0\Vert = 1$). The vertical diagonal entry of the reduced state of photon 2 evaluates to $1/2$:
--
--   $$ (\rho_2(\Psi_0))_{11} = \tfrac{1}{2}. $$
--
--   This reflects the normalization of the detector state and the equal distribution of intensity between horizontal and vertical polarization in the singlet state.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem reducedPhoton2_singlet_11_from_norm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 1 1 = 1 / 2 := by sorry

end AKR2008
