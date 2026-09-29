-- Prove2me | Theorems.Thm_BlockCycleRotation_four_mul_min_div_le_norm
-- name    : BlockCycleRotation.four_mul_min_div_le_norm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:52:19.312553+00:00
-- url     : https://prove2.me/theorems/a41ff058-62ec-4c78-a45f-7ead6d6a25a9
-- title:
--   The chord length at a nontrivial `a`-th root of unity
-- statement:
--   The chord length at a nontrivial `a`-th root of unity.
--
--   In Blomer–Bux this is **§4**, “Root-of-unity chord bound”. It is used in the proofs of `e_root_ne_one`, `two_div_norm_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Characters.lean#L68-L80

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.four_mul_min_div_le_norm {a m : ℕ} (h0 : 0 < m) (hma : m < a) :
    4 * ((min m (a - m) : ℕ) : ℝ) / (a : ℝ) ≤ ‖e (2 * π * m / a) - 1‖ := by sorry
