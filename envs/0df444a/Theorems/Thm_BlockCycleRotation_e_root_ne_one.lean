-- Prove2me | Theorems.Thm_BlockCycleRotation_e_root_ne_one
-- name    : BlockCycleRotation.e_root_ne_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:52:42.382407+00:00
-- url     : https://prove2.me/theorems/e51cf18c-9452-4291-8a90-6d22747ad260
-- title:
--   A nontrivial `a`-th root of unity is not `1`
-- statement:
--   A nontrivial `a`-th root of unity is not `1`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `norm_geom_sum_root_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Characters.lean#L82-L95

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.e_root_ne_one {a m : ℕ} (h0 : 0 < m) (hma : m < a) :
    e (2 * π * (m : ℝ) / a) ≠ 1 := by sorry
