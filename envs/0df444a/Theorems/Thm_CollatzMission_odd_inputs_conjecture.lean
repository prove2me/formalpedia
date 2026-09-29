-- Prove2me | Theorems.Thm_CollatzMission_odd_inputs_conjecture
-- name    : CollatzMission.odd_inputs_conjecture
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-08T03:46:14.25385+00:00
-- url     : https://prove2.me/theorems/3c35f5e0-0d93-4b0a-9401-72b2421896cd
-- title:
--   Collatz conjecture for positive odd inputs
-- statement:
--   For every positive odd integer $n$, there exists a nonnegative integer $m$ such that the $m$-fold iterate of the classical Collatz map sends $n$ to $1$.
--
--   Combined with the proved odd-input reduction, this statement implies the full Collatz conjecture.
-- source:
--   https://github.com/flound1129/collatz/blob/c0b24f073dcdc63d9d0974429bd8f3c522ed8eb4/lean/CollatzConjecture/Formulations.lean#L26-L28

import Definitions.Def_CollatzMission

namespace CollatzMission

theorem odd_inputs_conjecture : OddInputsConjecture := by
  sorry

end CollatzMission
