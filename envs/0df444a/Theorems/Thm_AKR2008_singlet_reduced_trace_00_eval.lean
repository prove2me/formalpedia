-- Prove2me | Theorems.Thm_AKR2008_singlet_reduced_trace_00_eval
-- name    : AKR2008.singlet_reduced_trace_00_eval
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:43:43.939257+00:00
-- url     : https://prove2.me/theorems/e59eead5-b5d4-4741-8e8f-0212181da75c
-- title:
--   Evaluation of reduced photon 2 state horizontal diagonal entry
-- statement:
--   Let $\mathcal H$ be a complex inner-product space (detector) and $\Phi_0 \in \mathcal H$ a normalized state ($\Vert\Phi_0\Vert = 1$). The horizontal diagonal entry of the reduced state of photon 2 evaluates to $1/2$:
--
--   $$ (\rho_2(\Psi_0))_{00} = \tfrac{1}{2}. $$
--
--   This explicit evaluation computes the partial trace over photon 1's horizontal and vertical states.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem singlet_reduced_trace_00_eval
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 0 0 = 1 / 2 := by sorry

end AKR2008
