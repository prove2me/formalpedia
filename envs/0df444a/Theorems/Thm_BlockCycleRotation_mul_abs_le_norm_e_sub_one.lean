-- Prove2me | Theorems.Thm_BlockCycleRotation_mul_abs_le_norm_e_sub_one
-- name    : BlockCycleRotation.mul_abs_le_norm_e_sub_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:51:13.861547+00:00
-- url     : https://prove2.me/theorems/97ca0656-23c5-46f8-9f6f-6c50345a52d7
-- title:
--   Jordan's inequality for the circle
-- statement:
--   **Jordan's inequality for the circle.** The hard half of Observation 17: for `|θ| ≤ π` we have `(2/π)|θ| ≤ ‖e θ - 1‖`. This is the bi-Lipschitz comparison between the arc-length and Euclidean metrics on the unit circle.
--
--   In Blomer–Bux this is **Obs. 17**, “Obs. 17: Jordan on the circle”. It is used in the proofs of `norm_geom_sum_le`, `norm_weighted_geom_sum_le_sharp`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Obs. 17. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/ExpSum.lean#L74-L95

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.mul_abs_le_norm_e_sub_one {θ : ℝ} (h : |θ| ≤ π) : 2 / π * |θ| ≤ ‖e θ - 1‖ := by sorry
