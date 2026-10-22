-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_collision_point_in_negative_boundary
-- name    : BirkhoffGlobalSection.left_collision_point_in_negative_boundary
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T12:38:55.69118+00:00
-- url     : https://prove2.me/theorems/b802aadf-cdd6-4163-9565-4e3a9333050c
-- title:
--   The selected collision point lies on the inner negative-energy boundary
-- statement:
--   For a mass ratio strictly between zero and one, the regularized left collision point has zero Hamiltonian, avoids the second collision, and is approachable from the negative-energy region connected to the origin. This identifies the base point of the boundary component.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 and the subcritical Hill-region geometry.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_collision_point_in_negative_boundary (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    leftCollisionPoint μ ∈ closure
      (connectedComponentIn
        {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
          0 < secondCollisionDistanceSq t}
        (fun _ : Fin 4 => (0 : ℝ))) ∧
      leviCivitaHamiltonian μ c (leftCollisionPoint μ) = 0 ∧
      0 < secondCollisionDistanceSq (leftCollisionPoint μ) := by sorry

end BirkhoffGlobalSection
