-- Prove2me | Theorems.Thm_BlockCycleRotation_norm_geom_sum_root_le
-- name    : BlockCycleRotation.norm_geom_sum_root_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:52:32.392672+00:00
-- url     : https://prove2.me/theorems/4f1c60b3-3ff8-4f9f-bc9e-19bc4dc1b4ac
-- title:
--   The bound §4 uses
-- statement:
--   **The bound §4 uses.** For `0 < m < a`, `‖∑_{B ≤ j < T} e(2πmj/a)‖ ≤ a / (2 · min(m, a-m))`.
--
--   In Blomer–Bux this is **§4**, “Sums at roots of unity”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Characters.lean#L116-L121

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.norm_geom_sum_root_le {a m : ℕ} (h0 : 0 < m) (hma : m < a) (B T : ℕ) :
    ‖∑ j ∈ Finset.Ico B T, e (2 * π * m / a) ^ j‖
      ≤ (a : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ)) := by sorry
