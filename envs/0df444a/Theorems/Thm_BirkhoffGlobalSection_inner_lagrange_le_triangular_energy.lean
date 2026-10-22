-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_le_triangular_energy
-- name    : BirkhoffGlobalSection.inner_lagrange_le_triangular_energy
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T18:59:09.673545+00:00
-- url     : https://prove2.me/theorems/333637a2-7918-44fc-aca2-d8a54ee22078
-- title:
--   Inner equilibrium energy does not exceed triangular energy
-- statement:
--   For $0<\mu<1$ and any inner collinear Lagrange equilibrium $L$, its Jacobi Hamiltonian satisfies $$H_\mu(L)\le -(3-\mu+\mu^2)/2.$$ The right-hand side is the common energy of the two triangular equilibria.
-- source:
--   Case decomposition of BirkhoffGlobalSection.inner_lagrange_minimizes_critical_energy on Prove2Me, using the Jacobi Hamiltonian in Definitions.Def_BirkhoffGlobalSection.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem inner_lagrange_le_triangular_energy (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase)
    (hL : IsInnerLagrangePoint μ L) :
    jacobiHamiltonian μ L ≤ -(3 - μ + μ ^ 2) / 2 := by sorry

end BirkhoffGlobalSection
