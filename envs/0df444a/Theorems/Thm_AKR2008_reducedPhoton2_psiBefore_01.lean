-- Prove2me | Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_01
-- name    : AKR2008.reducedPhoton2_psiBefore_01
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T22:48:37.669241+00:00
-- url     : https://prove2.me/theorems/ce188701-4ee6-4ef1-818c-b665b1642506
-- title:
--   Off-diagonal coherence (0, 1) of reduced photon 2 state vanishes
-- statement:
--   Let $\mathcal H$ be a complex inner-product space and $\Phi_0 \in \mathcal H$ a unit vector ($\Vert\Phi_0\Vert = 1$). The $(0, 1)$ matrix element of the reduced density operator of photon 2 vanishes:
--
--   $$ (\rho_2(\Psi_0))_{01} = \hat\rho_{01} = 0. $$
--
--   In the partial trace $\sum_{i\in\{0,1\}} \langle (\Psi_0)_{i1}, (\Psi_0)_{i0}\rangle_{\mathcal H}$, each term contains a zero component since $(\Psi_0)_{00} = 0$ and $(\Psi_0)_{11} = 0$, so no cross-polarization coherence persists.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem reducedPhoton2_psiBefore_01
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 0 1 = rhoHat 0 1 := by sorry

end AKR2008
