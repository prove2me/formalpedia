-- Prove2me | Theorems.Thm_AKR2008_singlet_reduced_trace_11_eval
-- name    : AKR2008.singlet_reduced_trace_11_eval
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:43:46.594375+00:00
-- url     : https://prove2.me/theorems/67d9c79c-b20e-40aa-b9a6-738f7203c16d
-- title:
--   Evaluation of reduced photon 2 state vertical diagonal entry
-- statement:
--   Let $\mathcal H$ be a complex inner-product space (detector) and $\Phi_0 \in \mathcal H$ a normalized state ($\Vert\Phi_0\Vert = 1$). The vertical diagonal entry of the reduced state of photon 2 evaluates to $1/2$:
--
--   $$ (\rho_2(\Psi_0))_{11} = \tfrac{1}{2}. $$
--
--   This explicit evaluation computes the partial trace over photon 1's horizontal and vertical states.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem singlet_reduced_trace_11_eval
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 1 1 = 1 / 2 := by sorry

end AKR2008
