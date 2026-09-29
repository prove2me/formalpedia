-- Prove2me | Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_11_of_zero
-- name    : AKR2008.reducedPhoton2_psiBefore_11_of_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:12:22.249072+00:00
-- url     : https://prove2.me/theorems/02121952-dec2-4878-8d1a-bf53933eb8aa
-- title:
--   Vertical reduced photon 2 population from vanishing parallel component
-- statement:
--   Let $\mathcal H$ be a complex inner-product space and $\Phi_0 \in \mathcal H$ a unit vector ($\Vert\Phi_0\Vert = 1$). If the parallel vertical component $(\Psi_0)_{11} = 0$, then the vertical diagonal entry of the reduced state of photon 2 equals $1/2$:
--
--   $$ (\rho_2(\Psi_0))_{11} = \tfrac{1}{2}. $$
--
--   This follows because tracing out photon 1 leaves all vertical population concentrated in the orthogonal term with weight $(1/\sqrt{2})^2 = 1/2$.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem reducedPhoton2_psiBefore_11_of_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1)
    (h : psiBefore Φ₀ 1 1 = 0) :
    reducedPhoton2 (psiBefore Φ₀) 1 1 = 1 / 2 := by sorry

end AKR2008
