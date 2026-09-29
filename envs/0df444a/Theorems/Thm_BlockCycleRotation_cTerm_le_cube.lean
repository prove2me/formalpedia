-- Prove2me | Theorems.Thm_BlockCycleRotation_cTerm_le_cube
-- name    : BlockCycleRotation.cTerm_le_cube
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:59:19.871459+00:00
-- url     : https://prove2.me/theorems/4e37a3da-bd5b-44f2-947a-ef7257008fad
-- title:
--   Sharper termwise bound
-- statement:
--   **Sharper termwise bound.** `cTerm ≤ 1/a³`.
--
--   In Blomer–Bux this is **§4**, “Sharper `cTerm ≤ 1/a³`, tail `≤ 1/N`”. It is used in the proof of `cTerm_row_le_sq`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Bound.lean#L19-L32

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.cTerm_le_cube (p : ℕ × ℕ) : cTerm p ≤ 1 / (p.1 : ℝ) ^ 3 := by sorry
