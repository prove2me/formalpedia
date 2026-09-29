-- Prove2me | Theorems.Thm_Erdos77_uniform_binomial_entropy_lower_bound
-- name    : Erdos77.uniform_binomial_entropy_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T13:06:29.33441+00:00
-- url     : https://prove2.me/theorems/5cbb901b-42e2-4e24-94ff-5e28051d49f3
-- title:
--   Uniform binomial entropy lower bound
-- statement:
--   There is one sublinear error xi such that for every pair of positive integers ell <= k, the binomial coefficient choose(k+ell, ell) is at least exp(k H(ell/k)-xi(k)), where H(x)=(1+x)log(1+x)-x log x.
-- source:
--   The standard entropy lower bound for binomial coefficients, obtained from the binomial distribution and Stirling asymptotics.

import Mathlib
import Definitions.Def_Erdos77_asymmetric_ramsey
open Filter Topology

namespace Erdos77
 theorem uniform_binomial_entropy_lower_bound :
  Exists fun xi : Nat -> Real =>
    xi =o[atTop] (fun k : Nat => (k : Real)) /\
    forall k ell : Nat, 0 < k -> 0 < ell -> ell <= k ->
      Real.exp ((((1 + ((ell : Real) / k)) * Real.log (1 + ((ell : Real) / k)) -
        ((ell : Real) / k) * Real.log ((ell : Real) / k)) * (k : Real)) - xi k) <=
        (Nat.choose (k + ell) ell : Real) := by sorry
end Erdos77
