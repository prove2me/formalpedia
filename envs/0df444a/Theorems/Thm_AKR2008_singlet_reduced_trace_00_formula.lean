-- Prove2me | Theorems.Thm_AKR2008_singlet_reduced_trace_00_formula
-- name    : AKR2008.singlet_reduced_trace_00_formula
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:40:37.389148+00:00
-- url     : https://prove2.me/theorems/9de591f9-0e5e-45b9-ad7e-56b2d5719166
-- title:
--   Formula for horizontal population of reduced photon 2 state
-- statement:
--   Let $\mathcal H$ be a complex inner-product space (detector) and $\Phi_0 \in \mathcal H$ a normalized state ($\Vert\Phi_0\Vert = 1$). Tracing out photon 1 and the detector from the pre-measurement state $|\Psi_0\rangle$ yields the horizontal population:
--
--   $$ (\rho_2(\Psi_0))_{00} = \tfrac{1}{2}. $$
--
--   This explicit formula represents the expectation value of the horizontal projector $|0\rangle\langle 0|$ on photon 2.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem singlet_reduced_trace_00_formula
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 0 0 = 1 / 2 := by sorry

end AKR2008
