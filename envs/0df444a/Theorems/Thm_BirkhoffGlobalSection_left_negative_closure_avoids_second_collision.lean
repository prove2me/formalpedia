-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_avoids_second_collision
-- name    : BirkhoffGlobalSection.left_negative_closure_avoids_second_collision
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T17:42:40.842562+00:00
-- url     : https://prove2.me/theorems/f0febc2a-c161-4810-b56b-75670452a618
-- title:
--   The inner negative-energy closure avoids the second collision
-- statement:
--   Below the first critical value, the closure of the regularized negative-energy component based at the origin stays a positive distance in the collision-distance-squared function from its zero set. The forbidden Hill barrier prevents approach to the second primary.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 and the subcritical Hill-region separation.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_negative_closure_avoids_second_collision (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ closure
      (connectedComponentIn
        {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
          0 < secondCollisionDistanceSq t}
        (fun _ : Fin 4 => (0 : ℝ))),
      0 < secondCollisionDistanceSq s := by sorry

end BirkhoffGlobalSection
