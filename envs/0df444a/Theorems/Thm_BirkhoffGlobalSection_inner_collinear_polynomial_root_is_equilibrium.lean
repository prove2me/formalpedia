-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inner_collinear_polynomial_root_is_equilibrium
-- name    : BirkhoffGlobalSection.inner_collinear_polynomial_root_is_equilibrium
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:39:37.882178+00:00
-- url     : https://prove2.me/theorems/c94e5fef-de07-4586-9efd-86e7d719f270
-- title:
--   Collinear force root yields an inner Lagrange equilibrium
-- statement:
--   If a position lies strictly between the primaries and solves the cleared-denominator collinear force balance, its phase point with zero vertical position and rotating-frame momentum (0,-x) is collision-free and critical for the Jacobi Hamiltonian.
-- source:
--   Joung--van Koert, Jacobi Hamiltonian equation (1.1), https://arxiv.org/abs/2407.19159v3; intermediate-value and gradient calculation for the inner collinear equilibrium.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- A root of the collinear force equation gives a collision-free inner equilibrium. -/
theorem inner_collinear_polynomial_root_is_equilibrium (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (x : ℝ)
    (hxlo : -μ < x) (hxhi : x < 1 - μ)
    (hpoly : x * (x + μ) ^ 2 * (1 - μ - x) ^ 2 -
      (1 - μ) * (1 - μ - x) ^ 2 + μ * (x + μ) ^ 2 = 0) :
    IsInnerLagrangePoint μ (![x, 0, 0, -x] : Phase) := by sorry

end BirkhoffGlobalSection
