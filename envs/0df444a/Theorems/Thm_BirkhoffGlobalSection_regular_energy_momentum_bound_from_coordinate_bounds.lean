-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_regular_energy_momentum_bound_from_coordinate_bounds
-- name    : BirkhoffGlobalSection.regular_energy_momentum_bound_from_coordinate_bounds
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T08:08:05.420954+00:00
-- url     : https://prove2.me/theorems/510a3c25-a28e-442b-8fa5-6f105b074cee
-- title:
--   Momentum coercivity of the regularized energy equation
-- statement:
--   Fix the mass ratio $\mu$, energy parameter $c$, and bounds $R_z$ and $\delta>0$. On the zero set of the Levi-Civita Hamiltonian, if both regularized position coordinates have absolute value at most $R_z$ and the distance to the right collision is at least $\delta$, then both momentum coordinates have absolute value at most a common constant $R_w$ depending only on these parameters. The energy equation is quadratic and coercive in momentum after its position-dependent linear terms are controlled.
-- source:
--   Joung--van Koert, Birkhoff global sections for the planar circular restricted three-body problem, https://arxiv.org/abs/2407.19159v3, equation (2.2), elementary coercivity consequence.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem regular_energy_momentum_bound_from_coordinate_bounds
    (μ c Rz δ : ℝ) (hδ : 0 < δ) :
    ∃ Rw : ℝ, ∀ s ∈ regularEnergyLocus μ c,
      |s 0| ≤ Rz → |s 1| ≤ Rz →
      δ ≤ Real.sqrt (secondCollisionDistanceSq s) →
      |s 2| ≤ Rw ∧ |s 3| ≤ Rw := by sorry

end BirkhoffGlobalSection
