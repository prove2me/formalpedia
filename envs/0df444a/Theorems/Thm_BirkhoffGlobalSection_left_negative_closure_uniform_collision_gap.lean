-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_uniform_collision_gap
-- name    : BirkhoffGlobalSection.left_negative_closure_uniform_collision_gap
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:06:40.948762+00:00
-- url     : https://prove2.me/theorems/e4115a8b-f7dc-4c92-a29b-9615c82356ae
-- title:
--   Uniform separation of the inner negative-energy closure from the second collision
-- statement:
--   The closure of the bounded negative-energy component based at the origin stays uniformly away from the second collision: its collision-distance-squared function has a strictly positive lower bound. A subunit Hill-circle position bound gives this separation.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Equation (2.2), Proposition 2.4 and the subcritical Hill-region geometry.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_negative_closure_uniform_collision_gap (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ closure
        (connectedComponentIn
          {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
            0 < secondCollisionDistanceSq t}
          (fun _ : Fin 4 => (0 : ℝ))),
        δ ≤ secondCollisionDistanceSq s := by sorry

end BirkhoffGlobalSection
