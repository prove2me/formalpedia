-- Prove2me | Theorems.Thm_Erdos77_diagonalRamsey_ge_one
-- name    : Erdos77.diagonalRamsey_ge_one
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T12:02:08.306985+00:00
-- url     : https://prove2.me/theorems/69bdcb1e-9d3a-41ff-a43d-ebc0bf5aa3f4
-- title:
--   Positive diagonal Ramsey numbers are at least one
-- statement:
--   For every positive integer k, the diagonal Ramsey number R(k), defined as the least size n for which every graph on n vertices has a k-clique or an independent k-set, is at least one.
-- source:
--   Immediate lower bound from the definition of the diagonal Ramsey number.

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey

namespace Erdos77
theorem diagonalRamsey_ge_one (k : Nat) (hk : 0 < k) :
    1 <= diagonalRamsey k := by sorry
end Erdos77
