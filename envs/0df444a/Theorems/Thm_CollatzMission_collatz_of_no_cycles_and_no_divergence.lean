-- Prove2me | Theorems.Thm_CollatzMission_collatz_of_no_cycles_and_no_divergence
-- name    : CollatzMission.collatz_of_no_cycles_and_no_divergence
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T03:45:41.397286+00:00
-- url     : https://prove2.me/theorems/322c714a-3188-404a-a3a5-083c02701799
-- title:
--   Cycle and non-cyclic counterexample reduction
-- statement:
--   Let $T$ be the classical Collatz map. Assume there is no positive orbit which avoids $1$ and eventually repeats, and no positive orbit which avoids $1$ without eventually repeating. Then every positive integer reaches $1$ under iteration of $T$.
--
--   Here the second branch means precisely a one-avoiding, non-eventually-cyclic orbit; it does not assert that the orbit is unbounded.
-- source:
--   https://github.com/flound1129/collatz/blob/c0b24f073dcdc63d9d0974429bd8f3c522ed8eb4/lean/CollatzConjecture/Formulations.lean#L154-L198

import Definitions.Def_CollatzMission

namespace CollatzMission

theorem collatz_of_no_cycles_and_no_divergence :
    NoEventualCycleCounterexamples →
      NoDivergentCounterexamples →
        ∀ n : ℕ, 0 < n → ∃ m : ℕ, collatzStep^[m] n = 1 := by
  sorry

end CollatzMission
