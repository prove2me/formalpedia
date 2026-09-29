-- Prove2me | Theorems.Thm_BlockCycleRotation_moveCount_fib
-- name    : BlockCycleRotation.moveCount_fib
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:52:36.516078+00:00
-- url     : https://prove2.me/theorems/5519d1ed-bcab-4076-a59d-dd698159d18f
-- title:
--   Observation 3: the Fibonacci worst case, $3n-5$ moves
-- statement:
--   For every $j$, taking $n = F_{j+4}$ and $k = F_{j+2}$ consecutive-but-one Fibonacci numbers,
--   $$\operatorname{moveCount}(n,k) = 3n - 5 .$$
--
--   This is Observation 3. Since $\gcd(F_{j+4},F_{j+2}) = 1$, the general bound of Theorem A reads $\operatorname{moveCount}(n,k) \le 3n-3$ here, so the Fibonacci family comes within two moves of the worst case and shows the constant $3$ cannot be improved.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Obs. 3. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Algorithm.lean#L272-L288

import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib

open BlockCycleRotation

theorem BlockCycleRotation.moveCount_fib (j : ℕ) :
    moveCount (Nat.fib (j + 4)) (Nat.fib (j + 2)) = 3 * Nat.fib (j + 4) - 5 := by sorry
