-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_le_right_outer_critical_energy
-- name    : BirkhoffGlobalSection.inner_lagrange_le_right_outer_critical_energy
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:19:02.884492+00:00
-- url     : https://prove2.me/theorems/2a89bcca-ebe1-4cef-8719-a2351f0647ef
-- title:
--   Inner versus right outer collinear equilibrium energy
-- statement:
--   For a mass parameter strictly between zero and one, the Jacobi Hamiltonian at the inner collinear Lagrange equilibrium is at most its value at any collision-free collinear critical point to the right of the right primary.
-- source:
--   Joung--van Koert, Jacobi Hamiltonian in equation (1.1), https://arxiv.org/abs/2407.19159v3; elementary one-dimensional comparison of collinear equilibrium energies.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Compare the inner equilibrium with a collinear equilibrium right of both primaries. -/
theorem inner_lagrange_le_right_outer_critical_energy (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase)
    (hL : IsInnerLagrangePoint μ L) (s : Phase)
    (hfree : collisionFree μ s)
    (hcrit : isCriticalPoint (jacobiHamiltonian μ) s)
    (haxis : s 1 = 0) (hright : 1 - μ < s 0) :
    jacobiHamiltonian μ L ≤ jacobiHamiltonian μ s := by sorry

end BirkhoffGlobalSection
