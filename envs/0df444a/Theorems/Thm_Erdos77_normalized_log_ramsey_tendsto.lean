-- Prove2me | Theorems.Thm_Erdos77_normalized_log_ramsey_tendsto
-- name    : Erdos77.normalized_log_ramsey_tendsto
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T20:27:39.859265+00:00
-- url     : https://prove2.me/theorems/caf2859b-e08e-492e-a036-e97cdb5d71d6
-- title:
--   Convergence of the normalized logarithmic Ramsey sequence
-- statement:
--   The logarithm of the diagonal Ramsey number, divided by its index, converges to a real limit as the index tends to infinity.
-- source:
--   Erdos Problem #77, https://www.erdosproblems.com/77; convergence component of the logarithmic growth limit statement.

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
open Filter Topology

namespace Erdos77
theorem normalized_log_ramsey_tendsto :
    Exists fun l : Real =>
      Filter.Tendsto
        (fun k : Nat => Real.log (diagonalRamsey k : Real) / (k : Real))
        atTop (nhds l) := by sorry
end Erdos77
