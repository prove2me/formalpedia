-- Prove2me | Theorems.Thm_BlockCycleRotation_norm_weighted_geom_sum_le
-- name    : BlockCycleRotation.norm_weighted_geom_sum_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:51:39.666905+00:00
-- url     : https://prove2.me/theorems/20495faf-cdc0-4aaf-81ae-cf7b9b21a6de
-- title:
--   Observation 17, weighted sum
-- statement:
--   **Observation 17, weighted sum.** For `0 < |θ| ≤ π`, `‖∑_{1 ≤ j < T} j · e(jθ)‖ ≤ (T - 1) · π / |θ|`. Proved by the paper's double-counting argument: write `j` as the number of `B` with `1 ≤ B ≤ j`, swap the order of summation, and apply the geometric bound to each inner sum.
--
--   In Blomer–Bux this is **Obs. 17**, “Obs. 17: weighted sum bound”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Obs. 17. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/ExpSum.lean#L167-L187

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.norm_weighted_geom_sum_le {θ : ℝ} (h0 : θ ≠ 0) (h : |θ| ≤ π) (T : ℕ) :
    ‖∑ j ∈ Finset.Ico 1 T, (j : ℂ) * e θ ^ j‖ ≤ (T - 1 : ℕ) * (π / |θ|) := by sorry
