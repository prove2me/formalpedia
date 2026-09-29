-- Prove2me | Theorems.Thm_BlockCycleRotation_zeta3_le
-- name    : BlockCycleRotation.zeta3_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:01:14.255069+00:00
-- url     : https://prove2.me/theorems/451ae8aa-c4b3-47fb-bc74-0736ed004e04
-- title:
--   $\zeta(3) \le 1.2023$
-- statement:
--   $$\zeta(3) \le \frac{12023}{10000} = 1.2023 .$$
--   A certified upper bound: the partial sum plus the tail estimate $\sum_{d>N} d^{-3} \le 1/(2N^2)$.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Remark 21. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Numeric.lean#L429-L436

import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

set_option maxHeartbeats 1000000 in
-- 50 rational terms of the series for `ζ(3)`.

theorem BlockCycleRotation.zeta3_le : zeta3 ≤ 12023 / 10000 := by sorry
