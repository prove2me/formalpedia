-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_le_left_outer_critical_energy
-- name    : BirkhoffGlobalSection.inner_lagrange_le_left_outer_critical_energy
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:18:57.125984+00:00
-- url     : https://prove2.me/theorems/92afdf6a-3f99-42aa-9102-41d7786c7969
-- title:
--   Inner versus left outer collinear equilibrium energy
-- statement:
--   For a mass parameter strictly between zero and one, the Jacobi Hamiltonian at the inner collinear Lagrange equilibrium is at most its value at any collision-free collinear critical point to the left of the left primary.
-- source:
--   Joung--van Koert, Jacobi Hamiltonian in equation (1.1), https://arxiv.org/abs/2407.19159v3; elementary one-dimensional comparison of collinear equilibrium energies.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Compare the inner equilibrium with a collinear equilibrium left of both primaries. -/
theorem inner_lagrange_le_left_outer_critical_energy (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase)
    (hL : IsInnerLagrangePoint μ L) (s : Phase)
    (hfree : collisionFree μ s)
    (hcrit : isCriticalPoint (jacobiHamiltonian μ) s)
    (haxis : s 1 = 0) (hleft : s 0 < -μ) :
    jacobiHamiltonian μ L ≤ jacobiHamiltonian μ s := by sorry

end BirkhoffGlobalSection
