-- Prove2me | Theorems.Thm_Erdos77_gnnw_uniform_ramsey_entropy_exponential_bound
-- name    : Erdos77.gnnw_uniform_ramsey_entropy_exponential_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T13:06:25.086761+00:00
-- url     : https://prove2.me/theorems/107d79c8-51dd-4891-859a-1ceffe273d80
-- title:
--   Uniform Ramsey bound with entropy factor
-- statement:
--   A single sublinear error w works uniformly for all positive integers ell <= k, bounding the asymmetric Ramsey number by exp((G(ell/k)+H(ell/k))k+w(k)), where G(x)=(-x/4+3x^2/100+2x^3/25)exp(-x) and H(x)=(1+x)log(1+x)-x log x.
-- source:
--   Gupta, Ndiaye, Norin, and Wei, Optimizing the CGMS upper bound on Ramsey numbers, arXiv:2407.19026, Theorem 1.

import Mathlib
import Definitions.Def_Erdos77_asymmetric_ramsey
open Filter Topology

namespace Erdos77
 theorem gnnw_uniform_ramsey_entropy_exponential_bound :
  Exists fun w : Nat -> Real =>
    w =o[atTop] (fun k : Nat => (k : Real)) /\
    forall k ell : Nat, 0 < k -> 0 < ell -> ell <= k ->
      (asymmetricRamsey k ell : Real) <=
        Real.exp (((-(1 / 4 : Real) * ((ell : Real) / k) +
            (3 / 100 : Real) * ((ell : Real) / k) ^ 2 +
            (2 / 25 : Real) * ((ell : Real) / k) ^ 3) *
            Real.exp (-((ell : Real) / k)) +
            ((1 + ((ell : Real) / k)) * Real.log (1 + ((ell : Real) / k)) -
              ((ell : Real) / k) * Real.log ((ell : Real) / k))) * (k : Real) + w k) := by sorry
end Erdos77
