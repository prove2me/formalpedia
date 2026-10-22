-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_point_exists
-- name    : BirkhoffGlobalSection.inner_lagrange_point_exists
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T18:52:45.443286+00:00
-- url     : https://prove2.me/theorems/8c07ceff-eb0f-445e-9d47-7c5f7140a03b
-- title:
--   Existence of the inner collinear Lagrange equilibrium
-- statement:
--   For every mass ratio $0<\mu<1$, there is a collision-free critical point of the Jacobi Hamiltonian whose configuration lies strictly on the line segment between the two primaries. This is the inner collinear Lagrange equilibrium $L_1$.
-- source:
--   Joung--van Koert, discussion of the first critical value and the inner Lagrange point preceding Proposition 2.4, https://arxiv.org/abs/2407.19159v3, PDF pp. 5–7.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- For physical masses the unique equilibrium on the open segment between
the two primaries gives an inner Lagrange point. -/
theorem inner_lagrange_point_exists (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    ∃ L : Phase, IsInnerLagrangePoint μ L := by sorry

end BirkhoffGlobalSection
