-- Prove2me | Theorems.Thm_BlockCycleRotation_avgCost_le_three_mul
-- name    : BlockCycleRotation.avgCost_le_three_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:52:42.635352+00:00
-- url     : https://prove2.me/theorems/e51c2e3c-5a95-4741-afb9-92db21c0f469
-- title:
--   The average cost is at most `3 * n`
-- statement:
--   **The average cost is at most `3 * n`.** Theorem 14 refines this to `D * n + O(n^(1/2+ε))` with `D ≈ 1.85`; see `theorem13` in `Theorem13.lean`.
--
--   The paper uses this step without giving it a number; the formalization records it as “Average `≤ 3n`”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Average.lean#L49-L62

import Definitions.Def_BlockCycleRotation_Average
import Mathlib

open BlockCycleRotation
open Finset

theorem BlockCycleRotation.avgCost_le_three_mul {n : ℕ} (hn : 0 < n) : avgCost n ≤ 3 * n := by sorry
