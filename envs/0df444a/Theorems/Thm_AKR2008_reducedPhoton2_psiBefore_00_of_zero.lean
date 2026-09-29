-- Prove2me | Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_00_of_zero
-- name    : AKR2008.reducedPhoton2_psiBefore_00_of_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:12:18.482346+00:00
-- url     : https://prove2.me/theorems/b3ef8fe7-34f6-43c5-ab29-9763ae7994c2
-- title:
--   Horizontal reduced photon 2 population from vanishing parallel component
-- statement:
--   Let $\mathcal H$ be a complex inner-product space and $\Phi_0 \in \mathcal H$ a unit vector ($\Vert\Phi_0\Vert = 1$). If the parallel horizontal component $(\Psi_0)_{00} = 0$, then the horizontal diagonal entry of the reduced state of photon 2 equals $1/2$:
--
--   $$ (\rho_2(\Psi_0))_{00} = \tfrac{1}{2}. $$
--
--   This follows because tracing out photon 1 leaves all horizontal population concentrated in the orthogonal term with weight $(1/\sqrt{2})^2 = 1/2$.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem reducedPhoton2_psiBefore_00_of_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1)
    (h : psiBefore Φ₀ 0 0 = 0) :
    reducedPhoton2 (psiBefore Φ₀) 0 0 = 1 / 2 := by sorry

end AKR2008
