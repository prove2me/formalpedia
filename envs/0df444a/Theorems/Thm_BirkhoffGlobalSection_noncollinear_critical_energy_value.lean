-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_noncollinear_critical_energy_value
-- name    : BirkhoffGlobalSection.noncollinear_critical_energy_value
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T18:59:06.754063+00:00
-- url     : https://prove2.me/theorems/ffcef5c8-dacd-40a3-b0b8-1dc3f8d14a2b
-- title:
--   Exact energy of a noncollinear equilibrium
-- statement:
--   For $0<\mu<1$, any collision-free critical point whose second position coordinate is nonzero has Jacobi energy $$H_\mu=-(3-\mu+\mu^2)/2.$$ The equilibrium equations force equal unit distances to the primaries and the triangular configuration, giving this explicit value.
-- source:
--   Case decomposition of BirkhoffGlobalSection.inner_lagrange_minimizes_critical_energy on Prove2Me, using the Jacobi Hamiltonian in Definitions.Def_BirkhoffGlobalSection.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem noncollinear_critical_energy_value (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (s : Phase)
    (hfree : collisionFree μ s)
    (hcrit : isCriticalPoint (jacobiHamiltonian μ) s)
    (hoffaxis : s 1 ≠ 0) :
    jacobiHamiltonian μ s = -(3 - μ + μ ^ 2) / 2 := by sorry

end BirkhoffGlobalSection
