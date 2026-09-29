-- Prove2me | Theorems.Thm_BlockCycleRotation_one_lt_dConst
-- name    : BlockCycleRotation.one_lt_dConst
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:59:43.149839+00:00
-- url     : https://prove2.me/theorems/87ca54ed-4cd3-497d-b240-13a930de776f
-- title:
--   `D > 1`, so the constant is not degenerate
-- statement:
--   `D > 1`, so the constant is not degenerate.
--
--   In Blomer–Bux this is **Remark 15**, “`1 < D`”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Remark 15. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Bound.lean#L102-L117

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.one_lt_dConst : 1 < dConst := by sorry
