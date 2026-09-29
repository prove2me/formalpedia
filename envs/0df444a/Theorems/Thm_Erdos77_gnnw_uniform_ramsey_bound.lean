-- Prove2me | Theorems.Thm_Erdos77_gnnw_uniform_ramsey_bound
-- name    : Erdos77.gnnw_uniform_ramsey_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T12:26:40.262002+00:00
-- url     : https://prove2.me/theorems/54fc2c82-197d-41ae-9f45-ded51f43f1e8
-- title:
--   Uniform off-diagonal Ramsey bound of Gupta–Ndiaye–Norin–Wei
-- statement:
--   There is one sublinear error function eta such that, uniformly for positive integers ell no greater than k, the off-diagonal Ramsey number is at most the central binomial factor times exp(G(ell/k) k + eta(k)), where G(x)=(-x/4+3x^2/100+2x^3/25) exp(-x).
-- source:
--   Gupta, Ndiaye, Norin, and Wei, Optimizing the CGMS upper bound on Ramsey numbers, arXiv:2407.19026, Theorem 1.

import Mathlib
import Definitions.Def_Erdos77_asymmetric_ramsey
open Filter Topology

namespace Erdos77

/-- Uniform off-diagonal form of the Gupta--Ndiaye--Norin--Wei bound. -/
theorem gnnw_uniform_ramsey_bound :
    Exists fun err : Nat -> Real =>
      err =o[atTop] (fun k : Nat => (k : Real)) /\
      forall k ell : Nat, 0 < k -> 0 < ell -> ell <= k ->
        (asymmetricRamsey k ell : Real) <=
          Real.exp (((-(1 / 4 : Real) * ((ell : Real) / k) +
            (3 / 100 : Real) * ((ell : Real) / k) ^ 2 +
            (2 / 25 : Real) * ((ell : Real) / k) ^ 3) *
            Real.exp (-((ell : Real) / k))) * (k : Real) + err k) *
            (Nat.choose (k + ell) ell : Real) := by
  sorry

end Erdos77
