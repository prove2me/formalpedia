-- Prove2me | Theorems.Thm_BlockCycleRotation_dConst_lt_two
-- name    : BlockCycleRotation.dConst_lt_two
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:59:43.035072+00:00
-- url     : https://prove2.me/theorems/51702cad-0572-41ec-be88-73b2a3e71983
-- title:
--   $D < 2$: block cycle beats trinity rotation on average
-- statement:
--   $$D < 2 .$$
--
--   Trinity rotation — the reverse-based scheme — uses essentially $2n$ moves. Since the block cycle algorithm uses $D\,n + O(n^{1/2+\varepsilon})$ moves on average, this strict inequality is the precise sense in which it is the cheaper scheme in the mean, and it is the remark the paper makes after Theorem 14.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Remark 15. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Bound.lean#L96-L100

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.dConst_lt_two : dConst < 2 := by sorry
