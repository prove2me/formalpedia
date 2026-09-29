-- Prove2me | Theorems.Thm_Erdos77_gnnw_diagonal_exponential_witness
-- name    : Erdos77.gnnw_diagonal_exponential_witness
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T12:00:33.751988+00:00
-- url     : https://prove2.me/theorems/6844aa36-3c61-41cc-9191-ed21fecba7e7
-- title:
--   Sublinear error form of the GNNW diagonal estimate
-- statement:
--   There is a real-valued error function err(k)=o(k) such that every diagonal Ramsey number is bounded by exp((-0.14/e)k + err(k)) times the central binomial coefficient choose(2k,k). This is the diagonal specialization of Theorem 1 of Gupta, Ndiaye, Norin, and Wei; the paper's o(k) term is represented explicitly.
-- source:
--   P. Gupta, N. Ndiaye, S. Norin, L. Wei, Optimizing the CGMS upper bound on Ramsey numbers, arXiv:2407.19026v2, Theorem 1 specialized to ell=k; https://arxiv.org/abs/2407.19026

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
open Filter Topology

namespace Erdos77
theorem gnnw_diagonal_exponential_witness :
    Exists fun err : Nat -> Real =>
      err =o[atTop] (fun k : Nat => (k : Real)) /\
      forall k : Nat,
        (diagonalRamsey k : Real) <=
          Real.exp ((- (0.14 : Real) / Real.exp 1) * (k : Real) + err k) *
            (Nat.choose (2 * k) k : Real) := by
  sorry
end Erdos77
