-- Prove2me | Theorems.Thm_BlockCycleRotation_moveCount_add_gcd_le
-- name    : BlockCycleRotation.moveCount_add_gcd_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:50:58.119765+00:00
-- url     : https://prove2.me/theorems/d7c799c8-be7d-411d-896b-edb5e7778e59
-- title:
--   Worst case, Theorem A
-- statement:
--   **Worst case, Theorem A.** The block cycle algorithm uses at most `3 * (n - gcd n k)` moves; in particular at most `3 * n`.
--
--   In Blomer–Bux this is **Thm A**, “Worst case `≤ 3(n − gcd)`, for `2k ≤ n`”. It is used in the proof of `moveCount_le_three_mul`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Thm A. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Euclid.lean#L133-L143

import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib

open BlockCycleRotation

theorem BlockCycleRotation.moveCount_add_gcd_le {n k : ℕ} (h : 2 * k ≤ n) :
    moveCount n k + 3 * Nat.gcd n k ≤ 3 * n := by sorry
