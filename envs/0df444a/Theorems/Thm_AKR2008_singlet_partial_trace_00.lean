-- Prove2me | Theorems.Thm_AKR2008_singlet_partial_trace_00
-- name    : AKR2008.singlet_partial_trace_00
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:24:00.416373+00:00
-- url     : https://prove2.me/theorems/2bf2df95-4fe0-4d0f-8b88-0c4d4ca59435
-- title:
--   Partial trace over photon 1 and detector yields 1/2 for (0, 0) entry
-- statement:
--   Let $\mathcal H$ be a complex inner-product space (detector) and $\Phi_0 \in \mathcal H$ a normalized state ($\Vert\Phi_0\Vert = 1$). The horizontal diagonal entry of the reduced state of photon 2 in the pre-measurement EPR state evaluates to $1/2$:
--
--   $$ (\rho_2(\Psi_0))_{00} = \tfrac{1}{2}. $$
--
--   This confirms that the partial trace over photon 1's polarization basis and the detector state leaves an unpolarized horizontal population of $1/2$.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem singlet_partial_trace_00
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 0 0 = 1 / 2 := by sorry

end AKR2008
