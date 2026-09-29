-- Prove2me | Theorems.Thm_BlockCycleRotation_cConst_le_seventeen_eightieths
-- name    : BlockCycleRotation.cConst_le_seventeen_eightieths
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:00:59.948159+00:00
-- url     : https://prove2.me/theorems/4ef2a9a1-ce4c-444e-b6ce-b531a026b5e0
-- title:
--   `C ≤ 17/80 = 0.2125`
-- statement:
--   **`C ≤ 17/80 = 0.2125`.**
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `dConst_le_185`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Numeric.lean#L254-L267

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem BlockCycleRotation.cConst_le_seventeen_eightieths : cConst ≤ 17 / 80 := by sorry
