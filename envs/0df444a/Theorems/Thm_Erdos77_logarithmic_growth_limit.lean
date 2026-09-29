-- Prove2me | Theorems.Thm_Erdos77_logarithmic_growth_limit
-- name    : Erdos77.logarithmic_growth_limit
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T09:46:03.822889+00:00
-- url     : https://prove2.me/theorems/5a9c8d1d-5e06-407f-ae4c-155fefa4fd50
-- title:
--   Existence of the normalized logarithmic Ramsey growth rate
-- statement:
--   There are an index N after which the diagonal Ramsey numbers are positive, and a real number l such that the normalized logarithms log(R(k))/k converge to l. This is the additive growth-rate form of the exponential-limit problem; positivity ensures the logarithm and real-power conversion behave as expected.
-- source:
--   Erdős Problem #77, https://www.erdosproblems.com/77

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
open Filter Topology

namespace Erdos77
theorem logarithmic_growth_limit :
    (Exists fun N : Nat => forall k : Nat, N <= k ->
      0 < (diagonalRamsey k : Real)) /\
    Exists fun l : Real =>
      Filter.Tendsto (fun k : Nat => Real.log (diagonalRamsey k : Real) / (k : Real))
        atTop (nhds l) := by sorry
end Erdos77
