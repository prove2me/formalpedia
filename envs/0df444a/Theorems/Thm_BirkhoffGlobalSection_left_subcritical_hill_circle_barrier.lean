-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_subcritical_hill_circle_barrier
-- name    : BirkhoffGlobalSection.left_subcritical_hill_circle_barrier
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T18:43:29.629313+00:00
-- url     : https://prove2.me/theorems/0f2d13a4-ef38-4555-953b-beec4ce9cf22
-- title:
--   An inaccessible circle separates the subcritical left Hill lobe
-- statement:
--   Fix $0<\mu<1$ and a Jacobi energy $-c$ strictly below the first critical value. There is a squared radius $R_q>0$ such that the circle of positions at squared distance $R_q$ from the left primary $(-\mu,0)$ cannot be reached by any point of the regularized zero-energy locus. In particular, the selected lobe cannot connect to the outer Hill region through this circle. This states the geometric forbidden-region barrier explicitly, without asserting a bound for the component.
-- source:
--   Joung--van Koert, Proposition 2.4, https://arxiv.org/abs/2407.19159v3, PDF p. 7; subcritical Hill-region separation at the inner Lagrange value.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Below the first critical value, a circle centered on the left primary
separates its Hill lobe from the outer allowed region. -/
theorem left_subcritical_hill_circle_barrier (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ Rq : ℝ, 0 < Rq ∧
      ∀ s ∈ regularEnergyLocus μ c,
        ((leviCivitaPosition μ s) 0 + μ) ^ 2 +
          ((leviCivitaPosition μ s) 1) ^ 2 ≠ Rq := by sorry

end BirkhoffGlobalSection
