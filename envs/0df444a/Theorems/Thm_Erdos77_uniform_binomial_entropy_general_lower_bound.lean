-- Prove2me | Theorems.Thm_Erdos77_uniform_binomial_entropy_general_lower_bound
-- name    : Erdos77.uniform_binomial_entropy_general_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T16:17:50.197721+00:00
-- url     : https://prove2.me/theorems/af81db79-12c1-4363-bc7f-57061c8880b6
-- title:
--   General binomial entropy lower bound
-- statement:
--   For positive integers a and b, the binomial coefficient choose(a+b,b) is at least exp((a+b) log(a+b) - a log(a) - b log(b)) divided by a+b+1. This follows by taking the b-th term of the binomial distribution with success probability b/(a+b): that term is a mode and therefore has mass at least 1/(a+b+1).
-- source:
--   Standard binomial entropy lower bound via the mode of the Binomial(a+b, b/(a+b)) distribution.

import Mathlib

namespace Erdos77
theorem uniform_binomial_entropy_general_lower_bound :
  forall a b : Nat, 0 < a -> 0 < b ->
    Real.exp (((((a + b : Nat) : Real) * Real.log ((a + b : Nat) : Real)) -
      ((a : Real) * Real.log (a : Real)) - ((b : Real) * Real.log (b : Real))) -
      Real.log ((a + b + 1 : Nat) : Real)) <= (Nat.choose (a + b) b : Real) := by sorry
end Erdos77
