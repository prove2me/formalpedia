-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_noncollinear_critical_equal_primary_distances
-- name    : BirkhoffGlobalSection.noncollinear_critical_equal_primary_distances
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T22:38:57.91502+00:00
-- url     : https://prove2.me/theorems/97b4fc60-70d5-4f31-af69-2cb37eff6fc2
-- title:
--   Equal primary distances at an off-axis equilibrium
-- statement:
--   For $0<\mu<1$, every collision-free Jacobi equilibrium away from the axis of the primaries has the same squared distance to each primary. The horizontal and vertical equilibrium equations imply equality of the inverse-cube gravitational factors.
-- source:
--   The planar circular restricted three-body Jacobi Hamiltonian, Joung--van Koert equation (1.1), https://arxiv.org/abs/2407.19159v3; standard triangular-equilibrium force balance.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The two primary distances agree at any off-axis Jacobi equilibrium. -/
theorem noncollinear_critical_equal_primary_distances (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (s : Phase)
    (hfree : collisionFree μ s)
    (hcrit : isCriticalPoint (jacobiHamiltonian μ) s)
    (hoffaxis : s 1 ≠ 0) :
    (s 0 + μ) ^ 2 + (s 1) ^ 2 =
      (s 0 - 1 + μ) ^ 2 + (s 1) ^ 2 := by sorry

end BirkhoffGlobalSection
