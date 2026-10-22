-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_noncollinear_critical_unit_distances
-- name    : BirkhoffGlobalSection.noncollinear_critical_unit_distances
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T19:05:11.239397+00:00
-- url     : https://prove2.me/theorems/67eeee2b-3fc3-412f-a46e-915500e583bb
-- title:
--   Unit distances at a noncollinear Jacobi equilibrium
-- statement:
--   For a physical mass ratio $0<\mu<1$, a collision-free Jacobi equilibrium away from the primaries’ axis is exactly one unit away from each primary. These two distance equations fix the equilateral configurations $L_4$ and $L_5$.
-- source:
--   Equilibrium equations of the Jacobi Hamiltonian (equation (1.1)) in Joung--van Koert, https://arxiv.org/abs/2407.19159v3; standard triangular Lagrange-point calculation.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- A collision-free equilibrium away from the primaries' axis lies at unit
distance from each primary, hence at an equilateral-triangle position. -/
theorem noncollinear_critical_unit_distances (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (s : Phase)
    (hfree : collisionFree μ s)
    (hcrit : isCriticalPoint (jacobiHamiltonian μ) s)
    (hoffaxis : s 1 ≠ 0) :
    (s 0 + μ) ^ 2 + (s 1) ^ 2 = 1 ∧
      (s 0 - 1 + μ) ^ 2 + (s 1) ^ 2 = 1 := by sorry

end BirkhoffGlobalSection
