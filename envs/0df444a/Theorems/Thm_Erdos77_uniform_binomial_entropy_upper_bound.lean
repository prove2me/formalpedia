-- Prove2me | Theorems.Thm_Erdos77_uniform_binomial_entropy_upper_bound
-- name    : Erdos77.uniform_binomial_entropy_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T14:20:54.045153+00:00
-- url     : https://prove2.me/theorems/abf1c8bb-d786-415d-a022-7e0799b0b46f
-- statement:
--   For positive integers k and ell with ell ? k, the binomial coefficient satisfies $\binom{k+\ell}{\ell} \le \exp(k((1+\ell/k)\log(1+\ell/k)-(\ell/k)\log(\ell/k)))$. This is the exact entropy upper estimate obtained by evaluating the binomial theorem at the probability ell/(k+ell).
-- source:
--   Standard binomial entropy estimate from the binomial theorem

import Mathlib
open Filter Topology

namespace Erdos77
theorem uniform_binomial_entropy_upper_bound :
  forall k ell : Nat, 0 < k -> 0 < ell -> ell <= k ->
    (Nat.choose (k + ell) ell : Real) <=
      Real.exp (((1 + ((ell : Real) / k)) * Real.log (1 + ((ell : Real) / k)) -
        ((ell : Real) / k) * Real.log ((ell : Real) / k)) * (k : Real)) := by
  sorry
end Erdos77
