-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_minimizes_critical_energy
-- name    : BirkhoffGlobalSection.inner_lagrange_minimizes_critical_energy
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T18:52:55.112818+00:00
-- url     : https://prove2.me/theorems/d16b8cb1-39ee-4101-85aa-10a995d9eea8
-- title:
--   Inner Lagrange energy is least among collision-free critical values
-- statement:
--   For every $0<\mu<1$, the Jacobi energy of an inner collinear Lagrange equilibrium is at most every collision-free critical value of the Jacobi Hamiltonian. This compares $L_1$ with all other equilibria, including the outer collinear and triangular points, and identifies it as the first energy at which a critical point occurs.
-- source:
--   Joung--van Koert, discussion of the first critical value and the inner Lagrange point preceding Proposition 2.4, https://arxiv.org/abs/2407.19159v3, PDF pp. 5–7.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The inner collinear equilibrium has no greater Jacobi Hamiltonian value
than any collision-free equilibrium, including the outer and triangular ones. -/
theorem inner_lagrange_minimizes_critical_energy (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase)
    (hL : IsInnerLagrangePoint μ L) :
    ∀ e ∈ criticalValueSet μ, jacobiHamiltonian μ L ≤ e := by sorry

end BirkhoffGlobalSection
