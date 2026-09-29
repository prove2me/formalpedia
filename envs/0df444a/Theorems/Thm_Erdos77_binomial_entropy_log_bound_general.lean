-- Prove2me | Theorems.Thm_Erdos77_binomial_entropy_log_bound_general
-- name    : Erdos77.binomial_entropy_log_bound_general
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T16:29:07.778682+00:00
-- url     : https://prove2.me/theorems/25bbc492-48bf-46f1-9bf5-e130f734ab5f
-- title:
--   General binomial entropy lower bound
-- statement:
--   For integers $0<r<n$, the binomial coefficient $\binom nr$ is at least $\exp(n\log n-r\log r-(n-r)\log(n-r)-\log(n+1))$. This is the entropy lower bound with a uniform denominator equal to the number of terms in the binomial distribution.
-- source:
--   General binomial entropy estimate from the binomial distribution; a standard mode-mass bound.

import Mathlib
open Filter Topology

namespace Erdos77
theorem binomial_entropy_log_bound_general (n r : Nat) (hr : 0 < r) (hrn : r < n) :
  Real.exp ((n : Real) * Real.log (n : Real) - (r : Real) * Real.log (r : Real) - (Nat.cast (n - r) : Real) * Real.log (Nat.cast (n - r) : Real) - Real.log ((n + 1 : Nat) : Real)) <= (Nat.choose n r : Real) := by sorry
end Erdos77
