-- Prove2me | Theorems.Thm_Erdos77_gnnw_diagonal_rate_exact
-- name    : Erdos77.gnnw_diagonal_rate_exact
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T10:44:19.435846+00:00
-- url     : https://prove2.me/theorems/7b29b192-1b24-4157-8649-66f2788303d0
-- title:
--   GNNW asymptotic diagonal rate at its optimized base
-- statement:
--   For every ε > 0, all sufficiently large k satisfy R(k) ≤ B^((1+ε)k), where B = 4 exp(-0.14/e), the optimized exponential base proved by Gupta, Ndiaye, Norin, and Wei. This is the asymptotic diagonal estimate R(k) ≤ B^(k+o(k)) in an epsilon formulation.
-- source:
--   P. Gupta, N. Ndiaye, S. Norin, L. Wei, Optimizing the CGMS upper bound on Ramsey numbers, arXiv:2407.19026v2, Theorem 1 specialized to ell=k and its optimized parameter.

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
open Filter Topology

namespace Erdos77

theorem gnnw_diagonal_rate_exact (eps : Real) (heps : 0 < eps) :
    Filter.Eventually
      (fun k : Nat =>
        (diagonalRamsey k : Real) <=
          (4 * Real.exp (- (0.14 : Real) / Real.exp 1)) ^ ((1 + eps) * (k : Real)))
      Filter.atTop := by
  sorry

end Erdos77
