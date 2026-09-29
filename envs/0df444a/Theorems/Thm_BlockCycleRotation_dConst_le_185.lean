-- Prove2me | Theorems.Thm_BlockCycleRotation_dConst_le_185
-- name    : BlockCycleRotation.dConst_le_185
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:01:18.907298+00:00
-- url     : https://prove2.me/theorems/02fb1220-8fd4-418a-9b15-7bb5160bbf20
-- title:
--   $D \le 1.85$, the value quoted in the paper
-- statement:
--   $$D = 1 + 4C \le 1.85 .$$
--   The paper quotes $D \approx 1.85$ for the average number of moves per element. This is the certified upper half of that claim, obtained from the alternative form $C = \tfrac12 - S/(2\zeta(3))$, the enclosure of $\zeta(3)$, and an explicit truncation of $S$.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Thm A / Thm 14. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Numeric.lean#L269-L274

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem BlockCycleRotation.dConst_le_185 : dConst ≤ 1.85 := by sorry
