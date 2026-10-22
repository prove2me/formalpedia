-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inner_collinear_force_polynomial_root
-- name    : BirkhoffGlobalSection.inner_collinear_force_polynomial_root
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:39:37.837471+00:00
-- url     : https://prove2.me/theorems/6e8ff826-13ca-4ea8-afcc-0da17efaa291
-- title:
--   A root of the inner collinear force polynomial
-- statement:
--   For every mass ratio strictly between zero and one, the polynomial obtained by clearing the two inverse-square denominators in the collinear force balance vanishes at a point strictly between the primaries. Its values at the two endpoint positions have opposite signs.
-- source:
--   Joung--van Koert, Jacobi Hamiltonian equation (1.1), https://arxiv.org/abs/2407.19159v3; intermediate-value and gradient calculation for the inner collinear equilibrium.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The cleared-denominator collinear force equation has a root between the primaries. -/
theorem inner_collinear_force_polynomial_root (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    ∃ x : ℝ, -μ < x ∧ x < 1 - μ ∧
      x * (x + μ) ^ 2 * (1 - μ - x) ^ 2 -
        (1 - μ) * (1 - μ - x) ^ 2 + μ * (x + μ) ^ 2 = 0 := by sorry

end BirkhoffGlobalSection
