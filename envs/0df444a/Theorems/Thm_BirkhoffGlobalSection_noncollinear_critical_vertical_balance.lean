-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_noncollinear_critical_vertical_balance
-- name    : BirkhoffGlobalSection.noncollinear_critical_vertical_balance
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T22:38:59.914965+00:00
-- url     : https://prove2.me/theorems/66c81b02-1b4d-4304-ac2e-05ac569bd1a4
-- title:
--   Vertical force balance at an off-axis equilibrium
-- statement:
--   At a collision-free Jacobi equilibrium with nonzero vertical position, the two gravitational inverse-cube factors obey $(1-\mu)/r_1^3+\mu/r_2^3=1$. The equality follows from the vertical position derivative after substituting the critical momentum.
-- source:
--   The planar circular restricted three-body Jacobi Hamiltonian, Joung--van Koert equation (1.1), https://arxiv.org/abs/2407.19159v3; standard triangular-equilibrium force balance.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Vertical force balance at an off-axis Jacobi equilibrium. -/
theorem noncollinear_critical_vertical_balance (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (s : Phase)
    (hfree : collisionFree μ s)
    (hcrit : isCriticalPoint (jacobiHamiltonian μ) s)
    (hoffaxis : s 1 ≠ 0) :
    (1 - μ) / (Real.sqrt ((s 0 + μ) ^ 2 + (s 1) ^ 2)) ^ 3 +
      μ / (Real.sqrt ((s 0 - 1 + μ) ^ 2 + (s 1) ^ 2)) ^ 3 = 1 := by sorry

end BirkhoffGlobalSection
