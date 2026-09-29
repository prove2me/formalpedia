-- Prove2me | Theorems.Thm_Erdos77_gnnw_optimized_base_lt_37993
-- name    : Erdos77.gnnw_optimized_base_lt_37993
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T10:44:50.732274+00:00
-- url     : https://prove2.me/theorems/75cbbd08-9b81-431d-a43d-d1242ed7fae1
-- title:
--   The optimized GNNW base is below 3.7993
-- statement:
--   The constant B = 4 exp(-0.14/e) from the optimized GNNW diagonal Ramsey estimate is strictly less than 3.7993.
-- source:
--   P. Gupta, N. Ndiaye, S. Norin, L. Wei, Optimizing the CGMS upper bound on Ramsey numbers, arXiv:2407.19026v2, optimized constant B = 4 exp(-0.14/e) = 3.799202739...

import Mathlib
open Real

namespace Erdos77

theorem gnnw_optimized_base_lt_37993 :
    4 * Real.exp (- (0.14 : Real) / Real.exp 1) < (3.7993 : Real) := by
  sorry

end Erdos77
