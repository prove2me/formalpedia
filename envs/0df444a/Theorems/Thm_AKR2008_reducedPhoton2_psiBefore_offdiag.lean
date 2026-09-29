-- Prove2me | Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_offdiag
-- name    : AKR2008.reducedPhoton2_psiBefore_offdiag
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T22:45:09.208296+00:00
-- url     : https://prove2.me/theorems/ffe61a0d-d9b9-4a62-8169-9387eb2c979d
-- title:
--   Off-diagonal entries (coherences) of the reduced photon 2 state vanish
-- statement:
--   Let $\mathcal H$ be a complex inner-product space and $\Phi_0 \in \mathcal H$ a unit vector ($\Vert\Phi_0\Vert = 1$). For any distinct polarization indices $j \neq j' \in \{0, 1\}$, the off-diagonal coherence of the reduced density operator of photon 2 vanishes:
--
--   $$ (\rho_2(\Psi_0))_{jj'} = \hat\rho_{jj'} = 0. $$
--
--   This confirms that tracing out photon 1 and the detector destroys all phase coherence between $|\uparrow\rangle$ and $|\downarrow\rangle$, leaving a diagonal statistical mixture.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem reducedPhoton2_psiBefore_offdiag
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) (j j' : Fin 2) (h : j ≠ j') :
    reducedPhoton2 (psiBefore Φ₀) j j' = rhoHat j j' := by sorry

end AKR2008
