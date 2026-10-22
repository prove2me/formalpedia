-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_nonpositive_regular_energy_momentum_bound
-- name    : BirkhoffGlobalSection.nonpositive_regular_energy_momentum_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:06:49.142571+00:00
-- url     : https://prove2.me/theorems/f953a5ac-0418-4ad6-bcd4-27bafcc4c6ae
-- title:
--   Quadratic momentum bound at nonpositive regularized energy
-- statement:
--   Fix position coordinates in a bounded box and bound the second-collision distance squared below by a positive constant. The regularized Hamiltonian has a positive definite quadratic leading term in momentum, so nonpositive energy forces both momentum coordinates to be uniformly bounded.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Equation (2.2), Proposition 2.4 and the subcritical Hill-region geometry.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem nonpositive_regular_energy_momentum_bound
    (μ c R δ : ℝ) (hδ : 0 < δ) :
    ∃ M : ℝ, ∀ s : Phase,
      |s 0| ≤ R → |s 1| ≤ R →
      δ ≤ secondCollisionDistanceSq s →
      leviCivitaHamiltonian μ c s ≤ 0 →
      |s 2| ≤ M ∧ |s 3| ≤ M := by sorry

end BirkhoffGlobalSection
