-- Prove2me | Theorems.Thm_Erdos77_gnnw_diagonal_rate_37993
-- name    : Erdos77.gnnw_diagonal_rate_37993
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T09:50:56.930581+00:00
-- url     : https://prove2.me/theorems/92f0ccc8-3d73-4d64-916a-98ba849fdd94
-- title:
--   GNNW diagonal rate: base 3.7993
-- statement:
--   For every real number eps > 0, for all sufficiently large k, the diagonal Ramsey number satisfies
--
--   $$R(k) \le 3.7993^{(1+\mathrm{eps})k}.$$
--
--   This slightly weakens the numerical base 3.7992... furnished by the GNNW 2024 diagonal estimate, while retaining a stronger rate than the milestone's base 3.8. It isolates the principal combinatorial and asymptotic estimate needed by the reduction.
-- source:
--   P. Gupta, N. Ndiaye, S. Norin, L. Wei, Optimizing the CGMS upper bound on Ramsey numbers, arXiv:2407.19026v2, Theorem 1 specialized to ell=k, with the uniform binomial entropy estimate; https://arxiv.org/abs/2407.19026

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
open Filter Topology

namespace Erdos77

theorem gnnw_diagonal_rate_37993 (eps : Real) (heps : 0 < eps) :
    Filter.Eventually
      (fun k : Nat =>
        (diagonalRamsey k : Real) <=
          (3.7993 : Real) ^ ((1 + eps) * (k : Real)))
      Filter.atTop := by
  sorry

end Erdos77
