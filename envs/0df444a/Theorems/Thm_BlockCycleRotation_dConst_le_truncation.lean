-- Prove2me | Theorems.Thm_BlockCycleRotation_dConst_le_truncation
-- name    : BlockCycleRotation.dConst_le_truncation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:00:37.6992+00:00
-- url     : https://prove2.me/theorems/3244878a-5b68-4ded-b35a-7b3bbf0b6b3c
-- title:
--   The same, for `D = 1 + 4C`
-- statement:
--   The same, for `D = 1 + 4C`.
--
--   In Blomer–Bux this is **Remark 21**, “Truncations bound `C`, `D` above”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Remark 21. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Remark21.lean#L697-L707

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem BlockCycleRotation.dConst_le_truncation (s : Finset (ℕ × ℕ)) :
    dConst ≤ 3 - 2 * (∑ p ∈ s, eTerm p) / zeta3 := by sorry
