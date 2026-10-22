-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_le_collinear_critical_energy
-- name    : BirkhoffGlobalSection.inner_lagrange_le_collinear_critical_energy
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T18:58:54.081485+00:00
-- url     : https://prove2.me/theorems/d0799847-b349-41d2-b3ee-4908475f783f
-- title:
--   Inner equilibrium energy is least among collinear critical points
-- statement:
--   For $0<\mu<1$, let $L$ be an inner Lagrange equilibrium. Every collision-free equilibrium on the axis of the two primaries has Jacobi energy at least $H_\mu(L)$. This isolates the comparison with the two exterior collinear equilibria, together with the inner-axis case.
-- source:
--   Case decomposition of BirkhoffGlobalSection.inner_lagrange_minimizes_critical_energy on Prove2Me, using the Jacobi Hamiltonian in Definitions.Def_BirkhoffGlobalSection.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem inner_lagrange_le_collinear_critical_energy (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase)
    (hL : IsInnerLagrangePoint μ L) (s : Phase)
    (hfree : collisionFree μ s)
    (hcrit : isCriticalPoint (jacobiHamiltonian μ) s)
    (haxis : s 1 = 0) :
    jacobiHamiltonian μ L ≤ jacobiHamiltonian μ s := by sorry

end BirkhoffGlobalSection
