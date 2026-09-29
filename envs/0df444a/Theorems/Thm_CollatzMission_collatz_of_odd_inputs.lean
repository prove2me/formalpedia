-- Prove2me | Theorems.Thm_CollatzMission_collatz_of_odd_inputs
-- name    : CollatzMission.collatz_of_odd_inputs
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T03:45:11.114836+00:00
-- url     : https://prove2.me/theorems/3ba526f2-a4e0-4ea0-acca-eac2e307a3b0
-- title:
--   Reduction to positive odd inputs
-- statement:
--   Let $T(n)=n/2$ when $n$ is even and $T(n)=3n+1$ when $n$ is odd. Assume every positive odd integer reaches $1$ after finitely many iterations of $T$. Then every positive integer reaches $1$ after finitely many iterations.
--
--   This reduction removes powers of two by strong induction and isolates the odd-input form of the Collatz conjecture.
-- source:
--   https://github.com/flound1129/collatz/blob/c0b24f073dcdc63d9d0974429bd8f3c522ed8eb4/lean/CollatzConjecture/Formulations.lean#L43-L80

import Definitions.Def_CollatzMission

namespace CollatzMission

theorem collatz_of_odd_inputs :
    OddInputsConjecture → ∀ n : ℕ, 0 < n → ∃ m : ℕ, collatzStep^[m] n = 1 := by
  sorry

end CollatzMission
