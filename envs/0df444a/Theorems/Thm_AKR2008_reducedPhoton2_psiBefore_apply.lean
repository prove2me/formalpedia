-- Prove2me | Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_apply
-- name    : AKR2008.reducedPhoton2_psiBefore_apply
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T22:32:54.184959+00:00
-- url     : https://prove2.me/theorems/35f1ad24-02df-4ad9-af09-b544dc937da4
-- title:
--   Entrywise reduced state of photon 2 before measurement
-- statement:
--   Let $\mathcal H$ be a complex inner-product space and let $\Phi_0 \in \mathcal H$ be a unit vector ($\Vert\Phi_0\Vert = 1$). For any polarization indices $j, j' \in \{0, 1\}$, the $(j, j')$-matrix entry of the reduced density operator of photon 2, obtained by tracing out photon 1 and the detector $\mathcal H$ from the state $|\Psi_0\rangle$, equals the corresponding entry of $\hat\rho$:
--
--   $$ (\rho_2(\Psi_0))_{jj'} = \hat\rho_{jj'}. $$
--
--   This evaluates the partial trace $\sum_{i\in\{0,1\}} \langle (\Psi_0)_{ij'}, (\Psi_0)_{ij}\rangle_{\mathcal H}$ explicitly across all four basis combinations $(0,0), (1,1), (0,1), (1,0)$.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem reducedPhoton2_psiBefore_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) (j j' : Fin 2) :
    reducedPhoton2 (psiBefore Φ₀) j j' = rhoHat j j' := by sorry

end AKR2008
