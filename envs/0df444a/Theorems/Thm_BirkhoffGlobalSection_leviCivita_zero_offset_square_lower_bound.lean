-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_leviCivita_zero_offset_square_lower_bound
-- name    : BirkhoffGlobalSection.leviCivita_zero_offset_square_lower_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T07:25:15.678986+00:00
-- url     : https://prove2.me/theorems/980da8af-dbbb-49e8-a34e-4f236bed0f39
-- title:
--   Momentum square lower bound for the Levi-Civita Hamiltonian
-- statement:
--   At any regularized phase point, completing the two momentum squares in the zero-offset Levi-Civita Hamiltonian gives a lower bound equal to minus the quadratic rotating-frame position contribution, minus half the left-primary mass, and minus the right-primary inverse-distance contribution.
-- source:
--   Joung--van Koert, regularized Hamiltonian equation (2.2) and Jacobi Hamiltonian equation (1.1), https://arxiv.org/abs/2407.19159v3; the circle comparison is used in Proposition 2.4.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Completing both momentum squares leaves the position-dependent effective potential. -/
theorem leviCivita_zero_offset_square_lower_bound (μ : ℝ) (s : Phase) :
    -(zNormSq s) *
        (((leviCivitaPosition μ s) 0) ^ 2 +
          ((leviCivitaPosition μ s) 1) ^ 2) / 2 -
      (1 - μ) / 2 -
      μ * zNormSq s / Real.sqrt (secondCollisionDistanceSq s) ≤
        leviCivitaHamiltonian μ 0 s := by sorry

end BirkhoffGlobalSection
