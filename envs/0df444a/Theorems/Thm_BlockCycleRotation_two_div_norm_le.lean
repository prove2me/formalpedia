-- Prove2me | Theorems.Thm_BlockCycleRotation_two_div_norm_le
-- name    : BlockCycleRotation.two_div_norm_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:52:21.383707+00:00
-- url     : https://prove2.me/theorems/22420dba-2dc5-4dee-b934-d32bd8ac0616
-- title:
--   The chord bound in the form the sum estimates use
-- statement:
--   The chord bound in the form the sum estimates use.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `norm_geom_sum_root_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Characters.lean#L97-L114

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.two_div_norm_le {a m : ℕ} (h0 : 0 < m) (hma : m < a) :
    2 / ‖e (2 * π * (m : ℝ) / a) - 1‖ ≤ (a : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ)) := by sorry
