-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_circle_effective_potential_bound
-- name    : BirkhoffGlobalSection.inner_lagrange_circle_effective_potential_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T07:25:28.230606+00:00
-- url     : https://prove2.me/theorems/06858251-dbcf-4d77-bd20-dd230a30c8a3
-- title:
--   Effective-potential comparison on the inner Lagrange circle
-- statement:
--   For physical mass ratio and an inner collinear Lagrange equilibrium, the position-only part of the zero-offset Levi-Civita Hamiltonian on the circle centered at the left primary through that equilibrium is at least the inner equilibrium energy multiplied by the squared regularized radius.
-- source:
--   Joung--van Koert, regularized Hamiltonian equation (2.2) and Jacobi Hamiltonian equation (1.1), https://arxiv.org/abs/2407.19159v3; the circle comparison is used in Proposition 2.4.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The position potential on the circle through the inner equilibrium is bounded by its value there. -/
theorem inner_lagrange_circle_effective_potential_bound (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase)
    (hL : IsInnerLagrangePoint μ L) (s : Phase)
    (hr : ((leviCivitaPosition μ s) 0 + μ) ^ 2 +
      ((leviCivitaPosition μ s) 1) ^ 2 = (L 0 + μ) ^ 2) :
    zNormSq s * jacobiHamiltonian μ L ≤
      -(zNormSq s) *
        (((leviCivitaPosition μ s) 0) ^ 2 +
          ((leviCivitaPosition μ s) 1) ^ 2) / 2 -
      (1 - μ) / 2 -
      μ * zNormSq s / Real.sqrt (secondCollisionDistanceSq s) := by sorry

end BirkhoffGlobalSection
