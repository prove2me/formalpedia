-- Prove2me | Theorems.Thm_Erdos77_diagonalRamsey_mul_bound
-- name    : Erdos77.diagonalRamsey_mul_bound
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-09-26T12:01:32.229477+00:00
-- url     : https://prove2.me/theorems/39c2b7cf-3e19-4801-8719-58ed36531ce3
-- title:
--   Product bound for diagonal Ramsey numbers
-- statement:
--   For positive integers m and n, the diagonal Ramsey number at m+n is at most the product of the diagonal Ramsey numbers at m and n. This is the diagonal form of the classical Ramsey product inequality.
-- source:
--   Erdos-Szekeres product inequality for Ramsey numbers; see https://www.erdosproblems.com/77

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey

namespace Erdos77
theorem diagonalRamsey_mul_bound (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    diagonalRamsey (m + n) <= diagonalRamsey m * diagonalRamsey n := by sorry
end Erdos77
