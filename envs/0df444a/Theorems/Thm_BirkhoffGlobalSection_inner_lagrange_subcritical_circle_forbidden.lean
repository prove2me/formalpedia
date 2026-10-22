-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_subcritical_circle_forbidden
-- name    : BirkhoffGlobalSection.inner_lagrange_subcritical_circle_forbidden
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T08:27:45.402074+00:00
-- url     : https://prove2.me/theorems/d0351972-9e98-431a-9368-db94ecc0fd3b
-- title:
--   Forbidden subcritical circle through the inner equilibrium
-- statement:
--   At energy below the first critical value, the regularized zero-energy locus avoids the position circle centered at the left primary and passing through the inner collinear equilibrium. The two primaries are one unit apart, so this circle has radius $r$ with $0<r<1$. Formally, every state on the regularized energy locus has squared distance from the left primary different from $r^2$. The Hamiltonian lower bound on this circle forces its energy above zero.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 and the effective potential bound on the circle through L1.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem inner_lagrange_subcritical_circle_forbidden (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ s ∈ regularEnergyLocus μ c,
        ((leviCivitaPosition μ s) 0 + μ) ^ 2 +
          ((leviCivitaPosition μ s) 1) ^ 2 ≠ r ^ 2 := by sorry

end BirkhoffGlobalSection
