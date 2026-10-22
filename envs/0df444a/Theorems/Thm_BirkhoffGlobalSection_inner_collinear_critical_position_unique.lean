-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inner_collinear_critical_position_unique
-- name    : BirkhoffGlobalSection.inner_collinear_critical_position_unique
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:18:59.122333+00:00
-- url     : https://prove2.me/theorems/02f9897c-9332-403f-a6f6-940d7c23de9e
-- title:
--   Uniqueness of the inner collinear equilibrium
-- statement:
--   For a fixed mass parameter strictly between zero and one, two collision-free critical points on the line between the two primaries have the same horizontal position. In particular, any such point has the position of the inner Lagrange equilibrium.
-- source:
--   Joung--van Koert, Jacobi Hamiltonian in equation (1.1), https://arxiv.org/abs/2407.19159v3; elementary one-dimensional comparison of collinear equilibrium energies.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- An equilibrium on the open interval between the primaries is the unique inner equilibrium. -/
theorem inner_collinear_critical_position_unique (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase)
    (hL : IsInnerLagrangePoint μ L) (s : Phase)
    (hfree : collisionFree μ s)
    (hcrit : isCriticalPoint (jacobiHamiltonian μ) s)
    (haxis : s 1 = 0) (hleft : -μ < s 0) (hright : s 0 < 1 - μ) :
    s 0 = L 0 := by sorry

end BirkhoffGlobalSection
