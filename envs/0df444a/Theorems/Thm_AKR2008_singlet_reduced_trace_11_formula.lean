-- Prove2me | Theorems.Thm_AKR2008_singlet_reduced_trace_11_formula
-- name    : AKR2008.singlet_reduced_trace_11_formula
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:40:39.040852+00:00
-- url     : https://prove2.me/theorems/f597961c-e044-4a82-9a8c-f017b35ac830
-- title:
--   Formula for vertical population of reduced photon 2 state
-- statement:
--   Let $\mathcal H$ be a complex inner-product space (detector) and $\Phi_0 \in \mathcal H$ a normalized state ($\Vert\Phi_0\Vert = 1$). Tracing out photon 1 and the detector from the pre-measurement state $|\Psi_0\rangle$ yields the vertical population:
--
--   $$ (\rho_2(\Psi_0))_{11} = \tfrac{1}{2}. $$
--
--   This explicit formula represents the expectation value of the vertical projector $|1\rangle\langle 1|$ on photon 2.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem singlet_reduced_trace_11_formula
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 1 1 = 1 / 2 := by sorry

end AKR2008
