-- Prove2me | Theorems.Thm_BlockCycleRotation_cost_le_three_mul
-- name    : BlockCycleRotation.cost_le_three_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:51:57.216216+00:00
-- url     : https://prove2.me/theorems/55032699-b6d8-4b41-a8d0-791a74bc55be
-- title:
--   Theorem A: the block cycle algorithm uses at most $3n$ moves
-- statement:
--   Let an array of $n$ elements be rotated in place by $k$ positions, with $2k \le n$. The **block cycle** scheme of Blomer–Bux performs the rotation by repeatedly exchanging a block of $k$ consecutive elements with an adjacent block, recursing on the shorter remaining segment; $\operatorname{cost}(n,k)$ counts the element moves it performs.
--
--   The theorem is the worst-case bound
--   $$\operatorname{cost}(n,k) \le 3n .$$
--
--   It is the algorithmic half of Theorem A. The sharper form proved alongside it is $\operatorname{cost}(n,k) + 3\gcd(n,k) \le 3n$, and Observation 3 shows the bound is essentially attained: on consecutive Fibonacci numbers the algorithm uses exactly $3n-5$ moves.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Thm A. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Algorithm.lean#L158-L161

import Definitions.Def_BlockCycleRotation_Algorithm
import Mathlib

open BlockCycleRotation

theorem BlockCycleRotation.cost_le_three_mul {n k : ℕ} (h : 2 * k ≤ n) : cost n k ≤ 3 * n := by sorry
