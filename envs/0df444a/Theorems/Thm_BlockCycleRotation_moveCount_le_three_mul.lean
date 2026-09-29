-- Prove2me | Theorems.Thm_BlockCycleRotation_moveCount_le_three_mul
-- name    : BlockCycleRotation.moveCount_le_three_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:51:06.504397+00:00
-- url     : https://prove2.me/theorems/5f14529e-ce41-4cb8-833a-b86e4ac604ed
-- title:
--   The block cycle algorithm never uses more than `3 * n` moves
-- statement:
--   The block cycle algorithm never uses more than `3 * n` moves.
--
--   In Blomer–Bux this is **Thm A**, “Worst case `≤ 3n`”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Thm A. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Euclid.lean#L145-L148

import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib

open BlockCycleRotation

theorem BlockCycleRotation.moveCount_le_three_mul {n k : ℕ} (h : 2 * k ≤ n) : moveCount n k ≤ 3 * n := by sorry
